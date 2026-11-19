#!/bin/sh
# Create a self-signed ECDSA P-256 certificate for localhost in conf/ (for the HTTPS server in
# conf/nginx.conf). Browsers will warn that it is self-signed; for a trusted local certificate
# use mkcert (https://github.com/FiloSottile/mkcert): mkcert -ecdsa -cert-file conf/localhost.crt
#   -key-file conf/localhost.key localhost 127.0.0.1
set -e
cd "$(dirname "$0")/../conf"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -keyout localhost.key -out localhost.crt -days 365 -subj /CN=localhost \
  -addext "subjectAltName=DNS:localhost,IP:127.0.0.1" 2>/dev/null
chmod 600 localhost.key
echo "wrote conf/localhost.crt and conf/localhost.key"
