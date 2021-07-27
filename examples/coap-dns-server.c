/* -*- Mode: C; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim:tabstop=2
 */

/* coap -- simple implementation of the Constrained Application Protocol (CoAP)
 *         as defined in RFC 7252
 *
 * Copyright (C) 2010--2021 Olaf Bergmann <bergmann@tzi.org> and others
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * This file is part of the CoAP library libcoap. Please see README for terms
 * of use.
 */

#include <limits.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>
#include <signal.h>
#ifdef _WIN32
#define strcasecmp _stricmp
#include "getopt.c"
#if !defined(S_ISDIR)
#define S_ISDIR(m) (((m) & S_IFMT) == S_IFDIR)
#endif
#ifndef R_OK
#define R_OK 4
#endif
static char* strndup(const char* s1, size_t n)
{
  char* copy = (char*)malloc(n + 1);
  if (copy) {
    memcpy(copy, s1, n);
    copy[n] = 0;
  }
  return copy;
};
#include <io.h>
#define access _access
#define fileno _fileno
#else
#include <unistd.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#endif

/* Need to refresh time once per sec */
#define COAP_RESOURCE_CHECK_TIME 1

#include <coap3/coap.h>

#ifndef min
#define min(a,b) ((a) < (b) ? (a) : (b))
#endif

/* temporary storage for dynamic resource representations */
static int quit = 0;

static int dns_socket;
static int dns_retries = 3U;

/*
 * For PKI, if one or more of cert_file, key_file and ca_file is in PKCS11 URI
 * format, then the remainder of cert_file, key_file and ca_file are treated
 * as being in DER format to provide consistency across the underlying (D)TLS
 * libraries.
 */
static char *cert_file = NULL; /* certificate and optional private key in PEM,
                                  or PKCS11 URI*/
static char *key_file = NULL; /* private key in PEM, DER or PKCS11 URI */
static char *pkcs11_pin = NULL; /* PKCS11 pin to unlock access to token */
static char *ca_file = NULL;   /* CA for cert_file - for cert checking in PEM,
                                  DER or PKCS11 URI */
static char *root_ca_file = NULL; /* List of trusted Root CAs in PEM */
static int use_pem_buf = 0; /* Map these cert/key files into memory to test
                               PEM_BUF logic if set */
static int is_rpk_not_cert = 0; /* Cert is RPK if set */
/* Used to hold initial PEM_BUF setup */
static uint8_t *cert_mem_base = NULL; /* certificate and private key in PEM_BUF */
static uint8_t *key_mem_base = NULL; /* private key in PEM_BUF */
static uint8_t *ca_mem_base = NULL;   /* CA for cert checking in PEM_BUF */
/* Used for verify_pki_sni_callback PEM_BUF temporary holding */
static uint8_t *cert_mem = NULL; /* certificate and private key in PEM_BUF */
static uint8_t *key_mem = NULL; /* private key in PEM_BUF */
static uint8_t *ca_mem = NULL;   /* CA for cert checking in PEM_BUF */
static size_t cert_mem_len = 0;
static size_t key_mem_len = 0;
static size_t ca_mem_len = 0;
static int verify_peer_cert = 1; /* PKI granularity - by default set */
#define MAX_KEY   64 /* Maximum length of a pre-shared key in bytes. */
static uint8_t *key = NULL;
static ssize_t key_length = 0;
int key_defined = 0;
static const char *hint = "CoAP";
static uint32_t block_mode = COAP_BLOCK_USE_LIBCOAP;

static coap_dtls_pki_t *
setup_pki(coap_context_t *ctx, coap_dtls_role_t role, char *sni);

typedef struct psk_sni_def_t {
  char* sni_match;
  coap_bin_const_t *new_key;
  coap_bin_const_t *new_hint;
} psk_sni_def_t;

typedef struct valid_psk_snis_t {
  size_t count;
  psk_sni_def_t *psk_sni_list;
} valid_psk_snis_t;

static valid_psk_snis_t valid_psk_snis = {0, NULL};

typedef struct id_def_t {
  char *hint_match;
  coap_bin_const_t *identity_match;
  coap_bin_const_t *new_key;
} id_def_t;

typedef struct valid_ids_t {
  size_t count;
  id_def_t *id_list;
} valid_ids_t;

static valid_ids_t valid_ids = {0, NULL};
typedef struct pki_sni_def_t {
  char* sni_match;
  char *new_cert;
  char *new_ca;
} pki_sni_def_t;

typedef struct valid_pki_snis_t {
  size_t count;
  pki_sni_def_t *pki_sni_list;
} valid_pki_snis_t;

static valid_pki_snis_t valid_pki_snis = {0, NULL};

/* SIGINT handler: set quit to 1 for graceful termination */
static void
handle_sigint(int signum COAP_UNUSED) {
  quit = 1;
}

#define RESPONSE { \
    0x93, 0x0f, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, \
    0x00, 0x00, 0x00, 0x00, 0x07, 0x65, 0x78, 0x61, \
    0x6d, 0x70, 0x6c, 0x65, 0x03, 0x6f, 0x72, 0x67, \
    0x00, 0x00, 0x1c, 0x00, 0x01, 0xc0, 0x0c, 0x00, \
    0x1c, 0x00, 0x01, 0x00, 0x00, 0xfe, 0x69, 0x00, \
    0x10, 0x26, 0x06, 0x28, 0x00, 0x02, 0x20, 0x00, \
    0x01, 0x02, 0x48, 0x18, 0x93, 0x25, 0xc8, 0x19, \
    0x46, \
}
#define COAP_MEDIATYPE_DNS_MESSAGE  65053U

static int decode_query(const uint8_t *base64_query, size_t *data_size,
                        const uint8_t **data);
static uint32_t min_ttl(const uint8_t *response_data, size_t response_len);
static coap_pdu_code_t resolve_query(uint8_t *query_data, size_t query_len,
                                     uint8_t *response_data, size_t *response_len);


static void
hnd_dns(coap_resource_t *resource,
        coap_session_t *session,
        const coap_pdu_t *request,
        const coap_string_t *query,
        coap_pdu_t *response) {
  coap_binary_t *body_data = NULL;
  coap_opt_iterator_t opt_iter;
  uint8_t *query_data = NULL;
  const uint8_t *base64_dns_query = NULL;
  coap_opt_t *option;
  coap_pdu_code_t code = coap_pdu_get_code(request);
  coap_pdu_code_t response_code = (code == (coap_pdu_code_t)COAP_REQUEST_FETCH)
                                ? COAP_RESPONSE_CODE_CONTENT
                                : COAP_RESPONSE_CODE_CREATED;
  uint16_t media_type = 0U;
  uint16_t accept_type = 0U;
  static uint8_t resp_payload[256];
  size_t base64_dns_query_len = 0;
  ssize_t resp_len = 0;

  coap_option_iterator_init(request, &opt_iter, COAP_OPT_ALL);

  while ((option = coap_option_next(&opt_iter))) {
    switch (opt_iter.number) {
    case COAP_OPTION_ACCEPT:
      accept_type = coap_decode_var_bytes(coap_opt_value(option),
                                          coap_opt_length(option));
      break;
    case COAP_OPTION_CONTENT_FORMAT:
      media_type = coap_decode_var_bytes(coap_opt_value(option),
                                         coap_opt_length(option));
      break;
    case COAP_OPTION_URI_QUERY:
      switch ((int)code) {
        case COAP_REQUEST_CODE_GET: {
            const uint8_t *value = coap_opt_value(option);
            if (memcmp(value, "dns=", sizeof("dns=") - 1) == 0) {
              base64_dns_query = &value[sizeof("dns=") - 1];
              base64_dns_query_len = coap_opt_length(option) - \
                                     (sizeof("dns=") - 1);
              media_type = COAP_MEDIATYPE_DNS_MESSAGE;
            }
            break;
          }
        default:
          break;
      }
      break;
    default:
      break;
    }
  }
  if ((accept_type != 0U) &&
      (accept_type != COAP_MEDIATYPE_DNS_MESSAGE)) {
    response_code = COAP_RESPONSE_CODE_NOT_ACCEPTABLE;
  }
  else if (media_type != COAP_MEDIATYPE_DNS_MESSAGE) {
    response_code = COAP_RESPONSE_CODE_UNSUPPORTED_CONTENT_FORMAT;
  }
  else {
    const uint8_t *data = query_data;
    size_t size, offset, total;

    switch ((int)code) {
      case COAP_REQUEST_CODE_GET:
        size = base64_dns_query_len;
        if (decode_query(base64_dns_query, &size, &data) < 0) {
          response_code = COAP_RESPONSE_CODE_BAD_REQUEST;
          goto response;
        }
        response_code = COAP_RESPONSE_CODE_CONTENT;
        break;
      case COAP_REQUEST_CODE_FETCH:
      case COAP_REQUEST_CODE_POST:
        if (coap_get_data_large(request, &size, &data, &offset, &total) &&
            size != total) {
          body_data = coap_block_build_body(body_data, size, data, offset, total);
          if (!body_data) {
            coap_log(LOG_DEBUG, "body build memory error\n");
            goto cleanup;
          }
          if ((offset + size) != total) {
            response_code = COAP_RESPONSE_CODE_CONTINUE;
          }
          data = body_data->s;
          size = body_data->length;
        }
        break;
      default:
        assert(0);
        /* should not be reached */
        break;
    }
    query_data = (uint8_t *)data;
    if (size < 12U) {   /* size is smaller than a DNS header */
      response_code = COAP_RESPONSE_CODE_BAD_REQUEST;
    }
    else {
      size_t tmp = sizeof(resp_payload);
      coap_pdu_code_t res = resolve_query(query_data, size, resp_payload, &tmp);
      if (res != 0) {
          response_code = res;
          resp_len = 0;
      }
      else {
          resp_len = tmp;
      }
    }
  }
  switch ((int)code) {
    case COAP_REQUEST_CODE_GET:
      if (query_data) {
        free((void *)query_data);
      }
      break;
    default:
      break;
  }
response: {
  uint32_t ttl = min_ttl(resp_payload, resp_len);
  int maxage = -1;

  if (ttl < UINT32_MAX) {
    /* readable TTL found */
    maxage = (int)(ttl > INT_MAX) ? INT_MAX : (int)ttl;
  }
  coap_pdu_set_code(response, response_code);
  coap_add_data_large_response(resource, session, request, response,
                               query, COAP_MEDIATYPE_DNS_MESSAGE,
                               maxage, 0, resp_len,
                               resp_payload, NULL, NULL);
  }
cleanup:
  coap_delete_binary(body_data);
}

static void
init_resources(coap_context_t *ctx) {
  coap_resource_t *r;

  r = coap_resource_init(NULL, 0);
  coap_register_handler(r, COAP_REQUEST_GET, hnd_dns);
  coap_register_handler(r, COAP_REQUEST_FETCH, hnd_dns);
  coap_register_handler(r, COAP_REQUEST_POST, hnd_dns);

  coap_add_attr(r, coap_make_str_const("ct"),
                coap_make_str_const("application/dns-message"), 0);
  coap_add_attr(r, coap_make_str_const("title"),
                coap_make_str_const("\"DNS-over-CoAPS Server\""), 0);
  coap_add_resource(ctx, r);
}

static int
verify_cn_callback(const char *cn,
                   const uint8_t *asn1_public_cert COAP_UNUSED,
                   size_t asn1_length COAP_UNUSED,
                   coap_session_t *session COAP_UNUSED,
                   unsigned depth,
                   int validated COAP_UNUSED,
                   void *arg
) {
  union {
    coap_dtls_role_t r;
    void *v;
  } role = { .v = arg };

  coap_log(LOG_INFO, "CN '%s' presented by %s (%s)\n",
           cn, role.r == COAP_DTLS_ROLE_SERVER ? "client" : "server",
           depth ? "CA" : "Certificate");
  return 1;
}

static uint8_t *read_file_mem(const char* file, size_t *length) {
  FILE *f;
  uint8_t *buf;
  struct stat statbuf;

  *length = 0;
  if (!file || !(f = fopen(file, "r")))
    return NULL;

  if (fstat(fileno(f), &statbuf) == -1) {
    fclose(f);
    return NULL;
  }

  buf = coap_malloc(statbuf.st_size+1);
  if (!buf) {
    fclose(f);
    return NULL;
  }

  if (fread(buf, 1, statbuf.st_size, f) != (size_t)statbuf.st_size) {
    fclose(f);
    coap_free(buf);
    return NULL;
  }
  buf[statbuf.st_size] = '\000';
  *length = (size_t)(statbuf.st_size + 1);
  fclose(f);
  return buf;
}

static void
update_pki_key(coap_dtls_key_t *dtls_key, const char *key_name,
               const char *cert_name, const char *ca_name) {;
  memset (dtls_key, 0, sizeof(*dtls_key));
  if ((key_name && strncasecmp (key_name, "pkcs11:", 7) == 0) ||
      (cert_name && strncasecmp (cert_name, "pkcs11:", 7) == 0) ||
      (ca_name && strncasecmp (ca_name, "pkcs11:", 7) == 0)) {
    dtls_key->key_type = COAP_PKI_KEY_PKCS11;
    dtls_key->key.pkcs11.public_cert = cert_name;
    dtls_key->key.pkcs11.private_key = key_name ?  key_name : cert_name;
    dtls_key->key.pkcs11.ca = ca_name;
    dtls_key->key.pkcs11.user_pin = pkcs11_pin;
  }
  else if (!use_pem_buf && !is_rpk_not_cert) {
    dtls_key->key_type = COAP_PKI_KEY_PEM;
    dtls_key->key.pem.public_cert = cert_name;
    dtls_key->key.pem.private_key = key_name ? key_name : cert_name;
    dtls_key->key.pem.ca_file = ca_name;
  }
  else {
    /* Map file into memory */
    coap_free(ca_mem);
    coap_free(cert_mem);
    coap_free(key_mem);
    ca_mem = read_file_mem(ca_name, &ca_mem_len);
    cert_mem = read_file_mem(cert_name, &cert_mem_len);
    key_mem = read_file_mem(key_name, &key_mem_len);

    dtls_key->key_type = COAP_PKI_KEY_PEM_BUF;
    dtls_key->key.pem_buf.ca_cert = ca_mem;
    dtls_key->key.pem_buf.public_cert = cert_mem;
    dtls_key->key.pem_buf.private_key = key_mem ? key_mem : cert_mem;
    dtls_key->key.pem_buf.ca_cert_len = ca_mem_len;
    dtls_key->key.pem_buf.public_cert_len = cert_mem_len;
    dtls_key->key.pem_buf.private_key_len = key_mem ?
                                             key_mem_len : cert_mem_len;
  }
}

static coap_dtls_key_t *
verify_pki_sni_callback(const char *sni,
                    void *arg COAP_UNUSED
) {
  static coap_dtls_key_t dtls_key;

  update_pki_key(&dtls_key, key_file, cert_file, ca_file);

  if (sni[0]) {
    size_t i;
    coap_log(LOG_INFO, "SNI '%s' requested\n", sni);
    for (i = 0; i < valid_pki_snis.count; i++) {
      /* Test for SNI to change cert + ca */
      if (strcasecmp(sni, valid_pki_snis.pki_sni_list[i].sni_match) == 0) {
        coap_log(LOG_INFO, "Switching to using cert '%s' + ca '%s'\n",
                 valid_pki_snis.pki_sni_list[i].new_cert,
                 valid_pki_snis.pki_sni_list[i].new_ca);
        update_pki_key(&dtls_key, valid_pki_snis.pki_sni_list[i].new_cert,
                       valid_pki_snis.pki_sni_list[i].new_cert,
                       valid_pki_snis.pki_sni_list[i].new_ca);
        break;
      }
    }
  }
  else {
    coap_log(LOG_DEBUG, "SNI not requested\n");
  }
  return &dtls_key;
}

static const coap_dtls_spsk_info_t *
verify_psk_sni_callback(const char *sni,
                    coap_session_t *c_session COAP_UNUSED,
                    void *arg COAP_UNUSED
) {
  static coap_dtls_spsk_info_t psk_info;

  /* Preset with the defined keys */
  memset (&psk_info, 0, sizeof(psk_info));
  psk_info.hint.s = (const uint8_t *)hint;
  psk_info.hint.length = hint ? strlen(hint) : 0;
  psk_info.key.s = key;
  psk_info.key.length = key_length;
  if (sni) {
    size_t i;
    coap_log(LOG_INFO, "SNI '%s' requested\n", sni);
    for (i = 0; i < valid_psk_snis.count; i++) {
      /* Test for identity match to change key */
      if (strcasecmp(sni,
                 valid_psk_snis.psk_sni_list[i].sni_match) == 0) {
        coap_log(LOG_INFO, "Switching to using '%.*s' hint + '%.*s' key\n",
                 (int)valid_psk_snis.psk_sni_list[i].new_hint->length,
                 valid_psk_snis.psk_sni_list[i].new_hint->s,
                 (int)valid_psk_snis.psk_sni_list[i].new_key->length,
                 valid_psk_snis.psk_sni_list[i].new_key->s);
        psk_info.hint = *valid_psk_snis.psk_sni_list[i].new_hint;
        psk_info.key = *valid_psk_snis.psk_sni_list[i].new_key;
        break;
      }
    }
  }
  else {
    coap_log(LOG_DEBUG, "SNI not requested\n");
  }
  return &psk_info;
}

static const coap_bin_const_t *
verify_id_callback(coap_bin_const_t *identity,
                   coap_session_t *c_session,
                   void *arg COAP_UNUSED
) {
  static coap_bin_const_t psk_key;
  const coap_bin_const_t *s_psk_hint = coap_session_get_psk_hint(c_session);
  const coap_bin_const_t *s_psk_key;
  size_t i;

  coap_log(LOG_INFO, "Identity '%.*s' requested, current hint '%.*s'\n", (int)identity->length,
           identity->s,
           s_psk_hint ? (int)s_psk_hint->length : 0,
           s_psk_hint ? (const char *)s_psk_hint->s : "");

  for (i = 0; i < valid_ids.count; i++) {
    /* Check for hint match */
    if (s_psk_hint &&
        strcmp((const char *)s_psk_hint->s,
               valid_ids.id_list[i].hint_match)) {
      continue;
    }
    /* Test for identity match to change key */
    if (coap_binary_equal(identity, valid_ids.id_list[i].identity_match)) {
      coap_log(LOG_INFO, "Switching to using '%.*s' key\n",
               (int)valid_ids.id_list[i].new_key->length,
               valid_ids.id_list[i].new_key->s);
      return valid_ids.id_list[i].new_key;
    }
  }

  s_psk_key = coap_session_get_psk_key(c_session);
  if (s_psk_key) {
    /* Been updated by SNI callback */
    psk_key = *s_psk_key;
    return &psk_key;
  }

  /* Just use the defined key for now */
  psk_key.s = key;
  psk_key.length = key_length;
  return &psk_key;
}

static coap_dtls_pki_t *
setup_pki(coap_context_t *ctx, coap_dtls_role_t role, char *client_sni) {
  static coap_dtls_pki_t dtls_pki;

  /* If general root CAs are defined */
  if (role == COAP_DTLS_ROLE_SERVER && root_ca_file) {
    struct stat stbuf;
    if ((stat(root_ca_file, &stbuf) == 0) && S_ISDIR(stbuf.st_mode)) {
      coap_context_set_pki_root_cas(ctx, NULL, root_ca_file);
    } else {
      coap_context_set_pki_root_cas(ctx, root_ca_file, NULL);
    }
  }

  memset (&dtls_pki, 0, sizeof(dtls_pki));
  dtls_pki.version = COAP_DTLS_PKI_SETUP_VERSION;
  if (ca_file || root_ca_file) {
    /*
     * Add in additional certificate checking.
     * This list of enabled can be tuned for the specific
     * requirements - see 'man coap_encryption'.
     *
     * Note: root_ca_file is setup separately using
     * coap_context_set_pki_root_cas(), but this is used to define what
     * checking actually takes place.
     */
    dtls_pki.verify_peer_cert        = verify_peer_cert;
    dtls_pki.check_common_ca         = !root_ca_file;
    dtls_pki.allow_self_signed       = 1;
    dtls_pki.allow_expired_certs     = 1;
    dtls_pki.cert_chain_validation   = 1;
    dtls_pki.cert_chain_verify_depth = 2;
    dtls_pki.check_cert_revocation   = 1;
    dtls_pki.allow_no_crl            = 1;
    dtls_pki.allow_expired_crl       = 1;
  }
  else if (is_rpk_not_cert) {
    dtls_pki.verify_peer_cert        = verify_peer_cert;
  }
  dtls_pki.is_rpk_not_cert        = is_rpk_not_cert;
  dtls_pki.validate_cn_call_back  = verify_cn_callback;
  dtls_pki.cn_call_back_arg       = (void*)role;
  dtls_pki.validate_sni_call_back = role == COAP_DTLS_ROLE_SERVER ?
                                    verify_pki_sni_callback : NULL;
  dtls_pki.sni_call_back_arg      = NULL;

  if (role == COAP_DTLS_ROLE_CLIENT) {
    dtls_pki.client_sni = client_sni;
  }

  update_pki_key(&dtls_pki.pki_key, key_file, cert_file, ca_file);
  /* Need to keep base initialization copies of any COAP_PKI_KEY_PEM_BUF */
  ca_mem_base = ca_mem;
  cert_mem_base = cert_mem;
  key_mem_base = key_mem;
  ca_mem = NULL;
  cert_mem = NULL;
  key_mem = NULL;
  return &dtls_pki;
}

static coap_dtls_spsk_t *
setup_spsk(void) {
  static coap_dtls_spsk_t dtls_spsk;

  memset (&dtls_spsk, 0, sizeof(dtls_spsk));
  dtls_spsk.version = COAP_DTLS_SPSK_SETUP_VERSION;
  dtls_spsk.validate_id_call_back = valid_ids.count ?
                                    verify_id_callback : NULL;
  dtls_spsk.validate_sni_call_back = valid_psk_snis.count ?
                                     verify_psk_sni_callback : NULL;
  dtls_spsk.psk_info.hint.s = (const uint8_t *)hint;
  dtls_spsk.psk_info.hint.length = hint ? strlen(hint) : 0;
  dtls_spsk.psk_info.key.s = key;
  dtls_spsk.psk_info.key.length = key_length;
  return &dtls_spsk;
}

static void
fill_keystore(coap_context_t *ctx) {

  if (cert_file == NULL && key_defined == 0) {
    if (coap_dtls_is_supported() || coap_tls_is_supported()) {
      coap_log(LOG_DEBUG,
               "(D)TLS not enabled as neither -k or -c options specified\n");
    }
    return;
  }
  if (cert_file) {
    coap_dtls_pki_t *dtls_pki = setup_pki(ctx,
                                          COAP_DTLS_ROLE_SERVER, NULL);
    if (!coap_context_set_pki(ctx, dtls_pki)) {
      coap_log(LOG_INFO, "Unable to set up %s keys\n",
               is_rpk_not_cert ? "RPK" : "PKI");
      /* So we do not set up DTLS */
      cert_file = NULL;
    }
  }
  if (key_defined) {
    coap_dtls_spsk_t *dtls_spsk = setup_spsk();

    coap_context_set_psk2(ctx, dtls_spsk);
  }
}

static void
usage( const char *program, const char *version) {
  const char *p;
  char buffer[72];
  const char *lib_version = coap_package_version();

  p = strrchr( program, '/' );
  if ( p )
    program = ++p;

  fprintf( stderr, "%s v%s -- a small CoAP implementation\n"
     "(c) 2010,2011,2015-2021 Olaf Bergmann <bergmann@tzi.org> and others\n\n"
     "%s\n"
     "%s\n"
    , program, version, lib_version,
    coap_string_tls_version(buffer, sizeof(buffer)));
  fprintf(stderr, "%s\n", coap_string_tls_support(buffer, sizeof(buffer)));
  fprintf(stderr, "\n"
     "Usage: %s [-g group] [-G group_if] [-l loss] [-p port]\n"
     "\t\t[-v num] [-A address] [-L value]\n"
     "\t\t[[-h hint] [-i match_identity_file] [-k key]\n"
     "\t\t[-s match_psk_sni_file]]]\n"
     "\t\t[[-c certfile] [-j keyfile] [-m] [-n] [-C cafile]\n"
     "\t\t[-J pkcs11_pin] [-M rpk_file] [-R trust_casfile]\n"
     "\t\t[-S match_pki_sni_file]]\n"
     "General Options\n"
     "\t-g group\tJoin the given multicast group\n"
     "\t       \t\tNote: DTLS over multicast is not currently supported\n"
     "\t-G group_if\tUse this interface for listening for the multicast\n"
     "\t       \t\tgroup. This can be different from the implied interface\n"
     "\t       \t\tif the -A option is used\n"
     "\t-l list\t\tFail to send some datagrams specified by a comma\n"
     "\t       \t\tseparated list of numbers or number ranges\n"
     "\t       \t\t(for debugging only)\n"
     "\t-l loss%%\tRandomly fail to send datagrams with the specified\n"
     "\t       \t\tprobability - 100%% all datagrams, 0%% no datagrams\n"
     "\t       \t\t(for debugging only)\n"
     "\t-p port\t\tListen on specified port for UDP and TCP. If (D)TLS is\n"
     "\t       \t\tenabled, then the coap-server will also listen on\n"
     "\t       \t\t 'port'+1 for DTLS and TLS.  The default port is 5683\n"
     "\t-v num \t\tVerbosity level (default 3, maximum is 9). Above 7,\n"
     "\t       \t\tthere is increased verbosity in GnuTLS and OpenSSL\n"
     "\t       \t\tlogging\n"
     "\t-A address\tInterface address to bind to\n"
     "\t-L value\tSum of one or more COAP_BLOCK_* flag valuess for block\n"
     "\t       \t\thandling methods. Default is 1 (COAP_BLOCK_USE_LIBCOAP)\n"
     "\t       \t\t(Sum of one or more of 1,2 and 4)\n"
    , program);
  fprintf( stderr,
     "PSK Options (if supported by underlying (D)TLS library)\n"
     "\t-h hint\t\tIdentity Hint to send. Default is CoAP. Zero length is\n"
     "\t       \t\tno hint\n"
     "\t-i match_identity_file\n"
     "\t       \t\tThis is a file that contains one or more lines of\n"
     "\t       \t\tIdentity Hints and (user) Identities to match for\n"
     "\t       \t\ta different new Pre-Shared Key (PSK) (comma separated)\n"
     "\t       \t\tto be used. E.g., per line\n"
     "\t       \t\t hint_to_match,identity_to_match,use_key\n"
     "\t       \t\tNote: -k still needs to be defined for the default case\n"
     "\t       \t\tNote: A match using the -s option may mean that the\n"
     "\t       \t\tcurrent Identity Hint is different to that defined by -h\n"
     "\t-k key \t\tPre-Shared Key. This argument requires (D)TLS with PSK\n"
     "\t       \t\tto be available. This cannot be empty if defined.\n"
     "\t       \t\tNote that both -c and -k need to be defined for both\n"
     "\t       \t\tPSK and PKI to be concurrently supported\n"
     "\t-s match_psk_sni_file\n"
     "\t       \t\tThis is a file that contains one or more lines of\n"
     "\t       \t\treceived Subject Name Identifier (SNI) to match to use\n"
     "\t       \t\ta different Identity Hint and associated Pre-Shared Key\n"
     "\t       \t\t(PSK) (comma separated) instead of the '-h hint' and\n"
     "\t       \t\t'-k key' options. E.g., per line\n"
     "\t       \t\t sni_to_match,use_hint,with_key\n"
     "\t       \t\tNote: -k still needs to be defined for the default case\n"
     "\t       \t\tif there is not a match\n"
     "\t       \t\tNote: The associated Pre-Shared Key will get updated if\n"
     "\t       \t\tthere is also a -i match.  The update checking order is\n"
     "\t       \t\t-s followed by -i\n"
     );
  fprintf(stderr,
     "PKI Options (if supported by underlying (D)TLS library)\n"
     "\tNote: If any one of '-c certfile', '-j keyfile' or '-C cafile' is in\n"
     "\tPKCS11 URI naming format (pkcs11: prefix), then any remaining non\n"
     "\tPKCS11 URI file definitions have to be in DER, not PEM, format.\n"
     "\tOtherwise all of '-c certfile', '-j keyfile' or '-C cafile' are in\n"
     "\tPEM format.\n\n"
     "\t-c certfile\tPEM file or PKCS11 URI for the certificate. The private\n"
     "\t       \t\tkey can also be in the PEM file, or has the same PKCS11\n"
     "\t       \t\tURI. If not, the private key is defined by '-j keyfile'.\n"
     "\t       \t\tNote that both -c and -k need to be defined for both\n"
     "\t       \t\tPSK and PKI to be concurrently supported\n"
     "\t-j keyfile\tPEM file or PKCS11 URI for the private key for the\n"
     "\t       \t\tcertificate in '-c certfile' if the parameter is\n"
     "\t       \t\tdifferent from certfile in '-c certfile'\n"
     "\t-m     \t\tUse COAP_PKI_KEY_PEM_BUF instead of COAP_PKI_KEY_PEM i/f\n"
     "\t       \t\tby reading into memory the Cert / CA file (for testing)\n"
     "\t-n     \t\tDisable remote peer certificate checking. This gives\n"
     "\t       \t\tclients the ability to use PKI, but without any defined\n"
     "\t       \t\tcertificates\n"
     "\t-C cafile\tPEM file or PKCS11 URI that contains a list of one or\n"
     "\t       \t\tmore CAs that are to be passed to the client for the\n"
     "\t       \t\tclient to determine what client certificate to use.\n"
     "\t       \t\tNormally, this list of CAs would be the root CA and and\n"
     "\t       \t\tany intermediate CAs. Ideally the server certificate\n"
     "\t       \t\tshould be signed by the same CA so that mutual\n"
     "\t       \t\tauthentication can take place. The contents of cafile\n"
     "\t       \t\tare added to the trusted store of root CAs.\n"
     "\t       \t\tUsing the -C or -R options will will trigger the\n"
     "\t       \t\tvalidation of the client certificate unless overridden\n"
     "\t       \t\tby the -n option\n"
     "\t-J pkcs11_pin\tThe user pin to unlock access to the PKCS11 token\n"
     "\t-M rpk_file\tRaw Public Key (RPK) PEM file or PKCS11 URI that\n"
     "\t       \t\tcontains both PUBLIC KEY and PRIVATE KEY or just\n"
     "\t       \t\tEC PRIVATE KEY. (GnuTLS and TinyDTLS(PEM) support only).\n"
     "\t       \t\t'-C cafile' or '-R trust_casfile' are not required\n"
     "\t-R trust_casfile\tPEM file containing the set of trusted root CAs\n"
     "\t       \t\tthat are to be used to validate the client certificate.\n"
     "\t       \t\tAlternatively, this can point to a directory containing\n"
     "\t       \t\ta set of CA PEM files.\n"
     "\t       \t\tUsing '-R trust_casfile' disables common CA mutual\n"
     "\t       \t\tauthentication which can only be done by using\n"
     "\t       \t\t'-C cafile'.\n"
     "\t       \t\tUsing the -C or -R options will will trigger the\n"
     "\t       \t\tvalidation of the client certificate unless overridden\n"
     "\t       \t\tby the -n option\n"
     "\t-S match_pki_sni_file\n"
     "\t       \t\tThis option denotes a file that contains one or more\n"
     "\t       \t\tlines of Subject Name Identifier (SNI) to match for new\n"
     "\t       \t\tCert file and new CA file (comma separated) to be used.\n"
     "\t       \t\tE.g., per line\n"
     "\t       \t\t sni_to_match,new_cert_file,new_ca_file\n"
     "\t       \t\tNote: -c and -C still need to be defined for the default\n"
     "\t       \t\tcase\n"
    );
}

static int
init_dns_socket(const char *dns_server, int dns_timeout)
{
  int sock, res;
  struct timeval tv = { .tv_sec = dns_timeout / 1000,
                        .tv_usec = (dns_timeout % 1000) * 1000 };
  struct addrinfo hints;
  struct addrinfo *result, *rp;

  memset(&hints, 0, sizeof(struct addrinfo));
  hints.ai_family = AF_UNSPEC;    /* Allow IPv4 or IPv6 */
  hints.ai_socktype = SOCK_DGRAM; /* Coap uses UDP */
  hints.ai_flags = AI_PASSIVE | AI_NUMERICHOST;

  res = getaddrinfo(dns_server, "53", &hints, &result);
  if ( res != 0 ) {
    fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(res));
    return res;
  }

  /* iterate through results until success */
  for (rp = result; rp != NULL; rp = rp->ai_next) {
    switch (rp->ai_family) {
        case AF_INET:
            if (rp->ai_addrlen < sizeof(struct sockaddr_in)) {
                continue;
            }
            break;
        case AF_INET6:
            if (rp->ai_addrlen < sizeof(struct sockaddr_in6)) {
                continue;
            }
            break;
        default:
            continue;
    }
    break;
  }
  if (rp == NULL) {
    fprintf(stderr, "no suitable result found\n");
    res = -1;
    goto finish;
  }
  sock = socket(rp->ai_family, SOCK_DGRAM, 0);
  if (sock < 0) {
    perror("Unable to create DNS socket");
    goto finish;
  }
  if ((res = connect(sock, rp->ai_addr, rp->ai_addrlen)) < 0) {
      perror("Unable to set peer for DNS socket");
      goto finish;
  }
  if ((res = setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv))) < 0) {
      perror("Unable to set timeout for DNS socket");
      goto finish;
  }
  dns_socket = sock;
  res = 0;
finish:
  freeaddrinfo(result);
  return res;
}

static coap_context_t *
get_context(const char *node, const char *port) {
  coap_context_t *ctx = NULL;
  int s;
  struct addrinfo hints;
  struct addrinfo *result, *rp;

  ctx = coap_new_context(NULL);
  if (!ctx) {
    return NULL;
  }
  /* Need PKI/RPK/PSK set up before we set up (D)TLS endpoints */
  fill_keystore(ctx);

  memset(&hints, 0, sizeof(struct addrinfo));
  hints.ai_family = AF_UNSPEC;    /* Allow IPv4 or IPv6 */
  hints.ai_socktype = SOCK_DGRAM; /* Coap uses UDP */
  hints.ai_flags = AI_PASSIVE | AI_NUMERICHOST;

  s = getaddrinfo(node, port, &hints, &result);
  if ( s != 0 ) {
    fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(s));
    coap_free_context(ctx);
    return NULL;
  }

  /* iterate through results until success */
  for (rp = result; rp != NULL; rp = rp->ai_next) {
    coap_address_t addr, addrs;
    coap_endpoint_t *ep_udp = NULL, *ep_dtls = NULL;

    if (rp->ai_addrlen <= (socklen_t)sizeof(addr.addr)) {
      coap_address_init(&addr);
      addr.size = (socklen_t)rp->ai_addrlen;
      memcpy(&addr.addr, rp->ai_addr, rp->ai_addrlen);
      addrs = addr;
      if (addr.addr.sa.sa_family == AF_INET) {
        uint16_t temp = ntohs(addr.addr.sin.sin_port) + 1;
        addrs.addr.sin.sin_port = htons(temp);
      } else if (addr.addr.sa.sa_family == AF_INET6) {
        uint16_t temp = ntohs(addr.addr.sin6.sin6_port) + 1;
        addrs.addr.sin6.sin6_port = htons(temp);
      } else {
        goto finish;
      }

      ep_udp = coap_new_endpoint(ctx, &addr, COAP_PROTO_UDP);
      if (ep_udp) {
        if (coap_dtls_is_supported() && (key_defined || cert_file)) {
          ep_dtls = coap_new_endpoint(ctx, &addrs, COAP_PROTO_DTLS);
          if (!ep_dtls)
            coap_log(LOG_CRIT, "cannot create DTLS endpoint\n");
        }
      } else {
        coap_log(LOG_CRIT, "cannot create UDP endpoint\n");
        continue;
      }
      if (coap_tcp_is_supported()) {
        coap_endpoint_t *ep_tcp;
        ep_tcp = coap_new_endpoint(ctx, &addr, COAP_PROTO_TCP);
        if (ep_tcp) {
          if (coap_tls_is_supported() && (key_defined || cert_file)) {
            coap_endpoint_t *ep_tls;
            ep_tls = coap_new_endpoint(ctx, &addrs, COAP_PROTO_TLS);
            if (!ep_tls)
              coap_log(LOG_CRIT, "cannot create TLS endpoint\n");
          }
        } else {
          coap_log(LOG_CRIT, "cannot create TCP endpoint\n");
        }
      }
      if (ep_udp)
        goto finish;
    }
  }

  fprintf(stderr, "no context available for interface '%s'\n", node);
  coap_free_context(ctx);
  ctx = NULL;

finish:
  freeaddrinfo(result);
  return ctx;
}

static ssize_t
cmdline_read_key(char *arg, unsigned char **buf, size_t maxlen) {
  size_t len = strnlen(arg, maxlen);
  if (len) {
    *buf = (unsigned char *)arg;
    return len;
  }
  /* Need at least one byte for the pre-shared key */
  coap_log( LOG_CRIT, "Invalid Pre-Shared Key specified\n" );
  return -1;
}

static int cmdline_read_psk_sni_check(char *arg) {
  FILE *fp = fopen(arg, "r");
  static char tmpbuf[256];
  if (fp == NULL) {
    coap_log(LOG_ERR, "SNI file: %s: Unable to open\n", arg);
    return 0;
  }
  while (fgets(tmpbuf, sizeof(tmpbuf), fp) != NULL) {
    char *cp = tmpbuf;
    char *tcp = strchr(cp, '\n');

    if (tmpbuf[0] == '#')
      continue;
    if (tcp)
      *tcp = '\000';

    tcp = strchr(cp, ',');
    if (tcp) {
      psk_sni_def_t *new_psk_sni_list;
      new_psk_sni_list = realloc(valid_psk_snis.psk_sni_list,
              (valid_psk_snis.count + 1)*sizeof (valid_psk_snis.psk_sni_list[0]));
      if (new_psk_sni_list == NULL) {
        break;
      }
      valid_psk_snis.psk_sni_list = new_psk_sni_list;
      valid_psk_snis.psk_sni_list[valid_psk_snis.count].sni_match = strndup(cp, tcp-cp);
      cp = tcp+1;
      tcp = strchr(cp, ',');
      if (tcp) {
        valid_psk_snis.psk_sni_list[valid_psk_snis.count].new_hint =
                             coap_new_bin_const((const uint8_t *)cp, tcp-cp);
        cp = tcp+1;
        valid_psk_snis.psk_sni_list[valid_psk_snis.count].new_key =
                             coap_new_bin_const((const uint8_t *)cp, strlen(cp));
        valid_psk_snis.count++;
      }
      else {
        free(valid_psk_snis.psk_sni_list[valid_psk_snis.count].sni_match);
      }
    }
  }
  fclose(fp);
  return valid_psk_snis.count > 0;
}

static int cmdline_read_identity_check(char *arg) {
  FILE *fp = fopen(arg, "r");
  static char tmpbuf[256];
  if (fp == NULL) {
    coap_log(LOG_ERR, "Identity file: %s: Unable to open\n", arg);
    return 0;
  }
  while (fgets(tmpbuf, sizeof(tmpbuf), fp) != NULL) {
    char *cp = tmpbuf;
    char *tcp = strchr(cp, '\n');

    if (tmpbuf[0] == '#')
      continue;
    if (tcp)
      *tcp = '\000';

    tcp = strchr(cp, ',');
    if (tcp) {
      id_def_t *new_id_list;
      new_id_list = realloc(valid_ids.id_list,
                          (valid_ids.count + 1)*sizeof (valid_ids.id_list[0]));
      if (new_id_list == NULL) {
        break;
      }
      valid_ids.id_list = new_id_list;
      valid_ids.id_list[valid_ids.count].hint_match = strndup(cp, tcp-cp);
      cp = tcp+1;
      tcp = strchr(cp, ',');
      if (tcp) {
        valid_ids.id_list[valid_ids.count].identity_match =
                               coap_new_bin_const((const uint8_t *)cp, tcp-cp);
        cp = tcp+1;
        valid_ids.id_list[valid_ids.count].new_key =
                           coap_new_bin_const((const uint8_t *)cp, strlen(cp));
        valid_ids.count++;
      }
      else {
        free(valid_ids.id_list[valid_ids.count].hint_match);
      }
    }
  }
  fclose(fp);
  return valid_ids.count > 0;
}

static int cmdline_read_pki_sni_check(char *arg) {
  FILE *fp = fopen(arg, "r");
  static char tmpbuf[256];
  if (fp == NULL) {
    coap_log(LOG_ERR, "SNI file: %s: Unable to open\n", arg);
    return 0;
  }
  while (fgets(tmpbuf, sizeof(tmpbuf), fp) != NULL) {
    char *cp = tmpbuf;
    char *tcp = strchr(cp, '\n');

    if (tmpbuf[0] == '#')
      continue;
    if (tcp)
      *tcp = '\000';

    tcp = strchr(cp, ',');
    if (tcp) {
      pki_sni_def_t *new_pki_sni_list;
      new_pki_sni_list = realloc(valid_pki_snis.pki_sni_list,
            (valid_pki_snis.count + 1)*sizeof (valid_pki_snis.pki_sni_list[0]));
      if (new_pki_sni_list == NULL) {
        break;
      }
      valid_pki_snis.pki_sni_list = new_pki_sni_list;
      valid_pki_snis.pki_sni_list[valid_pki_snis.count].sni_match =
                                                           strndup(cp, tcp-cp);
      cp = tcp+1;
      tcp = strchr(cp, ',');
      if (tcp) {
        int fail = 0;
        valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_cert =
                             strndup(cp, tcp-cp);
        cp = tcp+1;
        valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_ca =
                             strndup(cp, strlen(cp));
        if (access(valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_cert,
            R_OK)) {
          coap_log(LOG_ERR, "SNI file: Cert File: %s: Unable to access\n",
                   valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_cert);
          fail = 1;
        }
        if (access(valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_ca,
            R_OK)) {
          coap_log(LOG_ERR, "SNI file: CA File: %s: Unable to access\n",
                   valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_ca);
          fail = 1;
        }
        if (fail) {
          free(valid_pki_snis.pki_sni_list[valid_pki_snis.count].sni_match);
          free(valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_cert);
          free(valid_pki_snis.pki_sni_list[valid_pki_snis.count].new_ca);
        }
        else {
          valid_pki_snis.count++;
        }
      }
      else {
        coap_log(LOG_ERR,
                "SNI file: SNI_match,Use_Cert_file,Use_CA_file not defined\n");
        free(valid_pki_snis.pki_sni_list[valid_pki_snis.count].sni_match);
      }
    }
  }
  fclose(fp);
  return valid_pki_snis.count > 0;
}

int
main(int argc, char **argv) {
  coap_context_t  *ctx;
  const char *dns_server = "localhost";
  char *group = NULL;
  char *group_if = NULL;
  char addr_str[NI_MAXHOST] = "::";
  char port_str[NI_MAXSERV] = "5683";
  int opt;
  int dns_timeout = 1000;
  coap_log_t log_level = LOG_WARNING;
  unsigned wait_ms;
  int coap_fd;
  fd_set m_readfds;
  int nfds = 0;
  size_t i;
  uint16_t cache_ignore_options[] = { COAP_OPTION_BLOCK1,
                                      COAP_OPTION_BLOCK2,
                    /* See https://tools.ietf.org/html/rfc7959#section-2.10 */
                                      COAP_OPTION_MAXAGE,
                    /* See https://tools.ietf.org/html/rfc7959#section-2.10 */
                                      COAP_OPTION_IF_NONE_MATCH };
#ifndef _WIN32
  struct sigaction sa;
#endif

  while ((opt = getopt(argc, argv, "c:d:g:G:h:i:j:J:k:l:mnp:r:s:t:v:A:C:L:M:R:S:")) != -1) {
    switch (opt) {
    case 'A' :
      strncpy(addr_str, optarg, NI_MAXHOST-1);
      addr_str[NI_MAXHOST - 1] = '\0';
      break;
    case 'c' :
      cert_file = optarg;
      break;
    case 'd' :
      dns_server = optarg;
      break;
    case 'C' :
      ca_file = optarg;
      break;
    case 'g' :
      group = optarg;
      break;
    case 'G' :
      group_if = optarg;
      break;
    case 'h' :
      if (!optarg[0]) {
        hint = NULL;
        break;
      }
      hint = optarg;
      break;
    case 'i':
      if (!cmdline_read_identity_check(optarg)) {
        usage(argv[0], LIBCOAP_PACKAGE_VERSION);
        exit(1);
      }
      break;
    case 'j' :
      key_file = optarg;
      break;
    case 'J' :
      pkcs11_pin = optarg;
      break;
    case 'k' :
      key_length = cmdline_read_key(optarg, &key, MAX_KEY);
      if (key_length < 0) {
        break;
      }
      key_defined = 1;
      break;
    case 'l':
      if (!coap_debug_set_packet_loss(optarg)) {
        usage(argv[0], LIBCOAP_PACKAGE_VERSION);
        exit(1);
      }
      break;
    case 'L':
      block_mode = strtoul(optarg, NULL, 0);
      if (!(block_mode & COAP_BLOCK_USE_LIBCOAP)) {
        fprintf(stderr, "Block mode must include COAP_BLOCK_USE_LIBCOAP (1)\n");
        exit(-1);
      }
      break;
    case 'm':
      use_pem_buf = 1;
      break;
    case 'M':
      cert_file = optarg;
      is_rpk_not_cert = 1;
      break;
    case 'n':
      verify_peer_cert = 0;
      break;
    case 'p' :
      strncpy(port_str, optarg, NI_MAXSERV-1);
      port_str[NI_MAXSERV - 1] = '\0';
      break;
    case 'r':
        errno = 0;
        dns_retries = strtol(optarg, NULL, 10);
        if (errno != 0) {
            usage(argv[0], LIBCOAP_PACKAGE_VERSION);
            exit(1);
        }
        break;
    case 'R' :
      root_ca_file = optarg;
      break;
    case 's':
      if (!cmdline_read_psk_sni_check(optarg)) {
        usage(argv[0], LIBCOAP_PACKAGE_VERSION);
        exit(1);
      }
      break;
    case 'S':
      if (!cmdline_read_pki_sni_check(optarg)) {
        usage(argv[0], LIBCOAP_PACKAGE_VERSION);
        exit(1);
      }
      break;
    case 't':
        errno = 0;
        dns_timeout = strtol(optarg, NULL, 10);
        if (errno != 0) {
            usage(argv[0], LIBCOAP_PACKAGE_VERSION);
            exit(1);
        }
        break;
    case 'v' :
      log_level = strtol(optarg, NULL, 10);
      break;
    default:
      usage( argv[0], LIBCOAP_PACKAGE_VERSION );
      exit( 1 );
    }
  }

  coap_startup();
  coap_dtls_set_log_level(log_level);
  coap_set_log_level(log_level);

  init_dns_socket(dns_server, dns_timeout);

  ctx = get_context(addr_str, port_str);
  if (!ctx)
    return -1;

  init_resources(ctx);
  coap_context_set_block_mode(ctx, block_mode);

  /* Define the options to ignore when setting up cache-keys */
  coap_cache_ignore_options(ctx, cache_ignore_options,
             sizeof(cache_ignore_options)/sizeof(cache_ignore_options[0]));
  /* join multicast group if requested at command line */
  if (group)
    coap_join_mcast_group_intf(ctx, group, group_if);

  coap_fd = coap_context_get_coap_fd(ctx);
  if (coap_fd != -1) {
    /* if coap_fd is -1, then epoll is not supported within libcoap */
    FD_ZERO(&m_readfds);
    FD_SET(coap_fd, &m_readfds);
    nfds = coap_fd + 1;
  }

#ifdef _WIN32
  signal(SIGINT, handle_sigint);
#else
  memset (&sa, 0, sizeof(sa));
  sigemptyset(&sa.sa_mask);
  sa.sa_handler = handle_sigint;
  sa.sa_flags = 0;
  sigaction (SIGINT, &sa, NULL);
  sigaction (SIGTERM, &sa, NULL);
  /* So we do not exit on a SIGPIPE */
  sa.sa_handler = SIG_IGN;
  sigaction (SIGPIPE, &sa, NULL);
#endif

  wait_ms = COAP_RESOURCE_CHECK_TIME * 1000;

  while ( !quit ) {
    int result;

    if (coap_fd != -1) {
      /*
       * Using epoll.  It is more usual to call coap_io_process() with wait_ms
       * (as in the non-epoll branch), but doing it this way gives the
       * flexibility of potentially working with other file descriptors that
       * are not a part of libcoap.
       */
      fd_set readfds = m_readfds;
      struct timeval tv;
      coap_tick_t begin, end;

      coap_ticks(&begin);

      tv.tv_sec = wait_ms / 1000;
      tv.tv_usec = (wait_ms % 1000) * 1000;
      /* Wait until any i/o takes place or timeout */
      result = select (nfds, &readfds, NULL, NULL, &tv);
      if (result == -1) {
        if (errno != EAGAIN) {
          coap_log(LOG_DEBUG, "select: %s (%d)\n", coap_socket_strerror(), errno);
          break;
        }
      }
      if (result > 0) {
        if (FD_ISSET(coap_fd, &readfds)) {
          result = coap_io_process(ctx, COAP_IO_NO_WAIT);
        }
      }
      if (result >= 0) {
        coap_ticks(&end);
        /* Track the overall time spent in select() and coap_io_process() */
        result = (int)(end - begin);
      }
    }
    else {
      /*
       * epoll is not supported within libcoap
       *
       * result is time spent in coap_io_process()
       */
      result = coap_io_process( ctx, wait_ms );
    }
    if ( result < 0 ) {
      break;
    } else if ( result && (unsigned)result < wait_ms ) {
      /* decrement if there is a result wait time returned */
      wait_ms -= result;
    } else {
      /*
       * result == 0, or result >= wait_ms
       * (wait_ms could have decremented to a small value, below
       * the granularity of the timer in coap_io_process() and hence
       * result == 0)
       */
      wait_ms = COAP_RESOURCE_CHECK_TIME * 1000;
    }
  }

  close(dns_socket);
  coap_free(ca_mem);
  coap_free(cert_mem);
  coap_free(key_mem);
  coap_free(ca_mem_base);
  coap_free(cert_mem_base);
  coap_free(key_mem_base);
  for (i = 0; i < valid_psk_snis.count; i++) {
    free(valid_psk_snis.psk_sni_list[i].sni_match);
    coap_delete_bin_const(valid_psk_snis.psk_sni_list[i].new_hint);
    coap_delete_bin_const(valid_psk_snis.psk_sni_list[i].new_key);
  }
  if (valid_psk_snis.count)
    free(valid_psk_snis.psk_sni_list);

  for (i = 0; i < valid_ids.count; i++) {
    free(valid_ids.id_list[i].hint_match);
    coap_delete_bin_const(valid_ids.id_list[i].identity_match);
    coap_delete_bin_const(valid_ids.id_list[i].new_key);
  }
  if (valid_ids.count)
    free(valid_ids.id_list);

  for (i = 0; i < valid_pki_snis.count; i++) {
    free(valid_pki_snis.pki_sni_list[i].sni_match);
    free(valid_pki_snis.pki_sni_list[i].new_cert);
    free(valid_pki_snis.pki_sni_list[i].new_ca);
  }
  if (valid_pki_snis.count)
    free(valid_pki_snis.pki_sni_list);

  coap_free_context(ctx);
  coap_cleanup();

  return 0;
}

#define BASE64_CAPITAL_UPPER_BOUND     25     /**< base64 'Z'           */
#define BASE64_SMALL_UPPER_BOUND       51     /**< base64 'z'           */
#define BASE64_NUMBER_UPPER_BOUND      61     /**< base64 '9'           */
#define BASE64_MINUS                   62     /**< base64 '-'           */
#define BASE64_UNDERLINE               63     /**< base64 '_'           */
#define BASE64_NOT_DEFINED             0xFF   /**< no base64 symbol     */

static uint8_t getcode(char symbol)
{
    if (symbol == '-') {
      return BASE64_MINUS;
    }
    if ((symbol >= '0') && (symbol <= '9')) {
      return (symbol + (BASE64_NUMBER_UPPER_BOUND - '9'));
    }
    if ((symbol >= 'A') && (symbol <= 'Z')) {
      return (symbol - 'A');
    }
    if (symbol == '_') {
        return BASE64_UNDERLINE;
    }
    if ((symbol >= 'a') && (symbol <= 'z')) {
      return (symbol + (BASE64_SMALL_UPPER_BOUND - 'z'));
    }
    return BASE64_NOT_DEFINED;
}

static void decode_four_codes(uint8_t *out, const uint8_t *in)
{
    out[0] = (in[0] << 2) | (in[1] >> 4);
    out[1] = (in[1] << 4) | (in[2] >> 2);
    out[2] = (in[2] << 6) | in[3];
}

static int base64url_decode(const void *base64_in, size_t base64_in_size,
                            const uint8_t **data_out)
{
  uint8_t decode_buf[4U];
  uint8_t *out = malloc(((base64_in_size + 3) / 4) * 3);
  uint8_t *out_base = out;
  const uint8_t *in = base64_in;
  const uint8_t *end;
  size_t decode_buf_len = 0;

  assert(in);
  assert(out);
  end = in + base64_in_size;

  while (in < end) {
    decode_buf_len = 0;
    while ((decode_buf_len < sizeof(decode_buf)) && (in < end)) {
      switch (decode_buf[decode_buf_len] = getcode(*in++)) {
        case BASE64_NOT_DEFINED:
          continue;
        default:
          break;
      }
      decode_buf_len++;
    }
    if (in < end) {
      decode_four_codes(out, decode_buf);
      out += 3;
    }
  }
  switch (decode_buf_len) {
    case 0:
      /* no data in decode buffer -->nothing to do */
      break;
    case 2:
      /* Got two base64 chars, or one byte of output data.
       * The just fill with zero codes and ignore the two
       * additionally decoded bytes */
      decode_buf[2] = decode_buf[3] = 0U;
      decode_four_codes(out, decode_buf);
      out++;
      break;
    case 3:
      /* Got three base64 chars or 2 bytes of output data.
       * Again, just fill with zero bytes and ignore the
       * additionally decoded byte */
      decode_buf[3] = 0U;
      decode_four_codes(out, decode_buf);
      out += 2;
      break;
    case 4:
      /* Got full decode buffer that was not decoded yet, decode it */
      decode_four_codes(out, decode_buf);
      out += 3;
      break;
    default:
      /* cannot happen, (yes, even 1 and even when dropping ignored chars) */
      assert(0);
      free(out_base);
      errno = -EINVAL;
      return -1;
  }
  *data_out = out_base;
  return out - out_base;
}

static int decode_query(const uint8_t *base64_query, size_t *data_size,
                        const uint8_t **data)
{
  int res;

  if (base64_query == NULL) {
    fprintf(stderr, "No dns query found\n");
    return -1;
  }
  printf("Base64 DNS query to decode: %.*s\n", (int)*data_size, base64_query);
  res = base64url_decode(base64_query, *data_size, data);
  if (res < 0) {
    fprintf(stderr, "Unable to decode base64 %.*s\n", (int)*data_size,
            base64_query);
    return -1;
  }
  *data_size = res;
  return 0;
}

static ssize_t skip_hostname(const uint8_t *buf, size_t len, const uint8_t *ptr)
{
    const uint8_t *end = buf + len;
    unsigned res = 0;

    if (ptr >= end) {
        /* out-of-bound */
        return -EBADMSG;
    }
    /* handle DNS Message Compression */
    if (*ptr >= 192) {
        if ((ptr + 2) >= end) {
            return -EBADMSG;
        }
        return 2;
    }

    while (ptr[res]) {
        res += ptr[res] + 1;
        if ((&ptr[res]) >= end) {
            /* out-of-bound */
            return -EBADMSG;
        }
    }
    return res + 1;
}

typedef struct {
    uint16_t id;
    uint16_t flags;
    uint16_t qdcount;
    uint16_t ancount;
    uint16_t nscount;
    uint16_t arcount;
} dns_hdr_t;

static uint32_t get_long(const uint8_t *buf)
{
    uint32_t tmp;
    memcpy(&tmp, buf, sizeof(tmp));
    return tmp;
}

static uint16_t get_short(const uint8_t *buf)
{
    uint32_t tmp;
    memcpy(&tmp, buf, sizeof(tmp));
    return tmp;
}

static uint32_t min_ttl(const uint8_t *response_data, size_t response_len)
{
    const dns_hdr_t *hdr = (const dns_hdr_t *)response_data;
    const uint8_t *end = response_data + response_len;
    const uint8_t *ptr = response_data + sizeof(dns_hdr_t);
    uint32_t _min_ttl = UINT32_MAX;

    assert(response_len >= sizeof(dns_hdr_t));
    for (unsigned i = 0; i < ntohs(hdr->qdcount); i++) {
        ssize_t tmp = skip_hostname(response_data, response_len, ptr);
        if (tmp < 0) {
          return _min_ttl;
        }
        ptr += tmp;
        /* skip type and class of query */
        ptr += (2 * sizeof(uint16_t));
    }
    uint32_t rrcount = ntohs(hdr->ancount) + ntohs(hdr->nscount) +
                       ntohs(hdr->arcount);
    for (unsigned i = 0; i < rrcount; i++) {
      ssize_t tmp = skip_hostname(response_data, response_len, ptr);
      uint32_t ttl;
      uint16_t rdlength;

      if (tmp < 0) {
        /* abort parsing, use minimum TTL found so far */
        break;
      }
      ptr += tmp;
      /* remaining buffer to small to fit type (16 bit), class (16 bit),
       * ttl (32 bit), and rdlength (16 bit) */
      if ((ptr + ((3 * sizeof(uint16_t) + sizeof(uint32_t)))) >= end) {
        /* abort parsing, use minimum TTL found so far */
        break;
      }
      /* skip type and class of query */
      ptr += (2 * sizeof(uint16_t));
      ttl = ntohl(get_long(ptr));
      if (_min_ttl > ttl) {
        _min_ttl = ttl;
      }
      /* skip over TTL */
      ptr += sizeof(uint32_t);
      rdlength = ntohs(get_short(ptr));
      /* skip over rdata */
      ptr += sizeof(uint16_t) + rdlength;
    }
    return _min_ttl;
}

static coap_pdu_code_t resolve_query(uint8_t *query_data, size_t query_len,
                                     uint8_t *response_data, size_t *response_len)
{
  ssize_t res;
  int retries = dns_retries;
  uint16_t tid = (uint16_t)rand();
  uint8_t orig_tid[] = {
      query_data[0],
      query_data[1],
  };

  query_data[0] = tid >> 8;
  query_data[1] = tid & 0xff;
  errno = EAGAIN;
  do {
    if ((errno == EAGAIN) && (retries > 0)) {
      if (send(dns_socket, query_data, query_len, 0) < 0) {
        perror("Unable to send DNS query to DNS server");
      }
      /* TODO do asynchronously and send empty ACK to client to prevent
       * retransmissions */
    }
    else {
        perror("Unable to receive DNS response, replying with SERVFAIL");
        memcpy(response_data, query_data, query_len);
        response_data[2] = 0x81;
        response_data[3] = 0x82;
        res = query_len;
    }
    perror("Retrying");
  } while ((retries-- > 0) && ((res = recv(
      dns_socket, response_data, *response_len, 0
    )) < 0) && (res < (int)sizeof(dns_hdr_t)) &&
           (response_data[0] != (tid >> 8)) &&
           (response_data[1] != (tid & 0xff)));
  /* should be assert by while check */
  assert(res >= (int)sizeof(dns_hdr_t));
  response_data[0] = orig_tid[0];
  response_data[1] = orig_tid[1];
  *response_len = res;
  return 0;
}
