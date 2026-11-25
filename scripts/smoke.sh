#!/bin/sh
# End-to-end smoke check of a built lnginx binary against the sample site in ./html.
# Not where correctness comes from (that is LeanNginx/Spec.lean); it checks the IO shell.
# Usage: scripts/smoke.sh [path/to/lnginx]
set -u
cd "$(dirname "$0")/.."
BIN=${1:-.lake/build/bin/lnginx}
PORT=18089
UP=18090
TLSPORT=18091
TMP=$(mktemp -d)
trap 'kill $SRV $UPS 2>/dev/null; rm -rf "$TMP"' EXIT
mkdir -p "$TMP/up" && echo "from upstream" > "$TMP/up/u.txt"
[ -f html/files/random.bin ] || head -c 300000 /dev/urandom > html/files/random.bin
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes -keyout "$TMP/ec.key" \
  -out "$TMP/ec.crt" -days 2 -subj /CN=localhost -addext "subjectAltName=DNS:localhost" 2>/dev/null
openssl req -x509 -newkey rsa:2048 -nodes -keyout "$TMP/rsa.key" -out "$TMP/rsa.crt" -days 2 \
  -subj /CN=rsa.test -addext "subjectAltName=DNS:rsa.test" 2>/dev/null
python3 -c "print('<p>compress me</p>' * 2000)" > "$TMP/page.html"
echo "smoke:$(openssl passwd -5 hunter2)" > "$TMP/users"
mkdir -p "$TMP/site/q" "$TMP/site/secret" "$TMP/ls"
echo "games" > "$TMP/site/q/games.html"; echo "secret page" > "$TMP/site/secret/s.html"
touch "$TMP/ls/javascript:alert(1)"
python3 -m http.server $UP --bind 127.0.0.1 --directory "$TMP/up" >/dev/null 2>&1 & UPS=$!
cat > "$TMP/t.conf" <<CONF
http {
  include $(pwd)/conf/mime.types;
  access_log $TMP/access.log;
  server {
    listen 127.0.0.1:$PORT;
    server_name localhost;
    root $(pwd)/html;
    location / { try_files \$uri \$uri/ =404; }
    location /files/ { autoindex on; }
    location /img { alias $(pwd)/html/files/; }
    location /api/ { proxy_pass http://127.0.0.1:$UP/; }
    location = /health { default_type text/plain; return 200 "ok\n"; }
    location = /gone { return 410; }
    location ~* \.(gif|jpe?g)$ { return 200 "regex\n"; }
    location ^~ /pics/ { return 200 "noregex\n"; }
    location /gz/ { alias $TMP/; gzip on; gzip_types text/css; }
    location /old/ { return 301 /; }
    location /private/ { alias $TMP/up/; auth_basic "smoke"; auth_basic_user_file $TMP/users; }
    location = /cat { root $TMP/site; try_files /q/\$args.html =404; }
    location /q/ { root $TMP/site; }
    location /secret/ { root $TMP/site; auth_basic "smoke"; auth_basic_user_file $TMP/users; }
    location /ls/ { alias $TMP/ls/; autoindex on; }
    error_page 404 /404.html;
  }
  server { listen 127.0.0.1:$PORT; server_name *.vhost.test; return 200 "vhost \$host\n"; }
  server {
    listen 127.0.0.1:$TLSPORT ssl; server_name localhost; root $(pwd)/html;
    ssl_certificate $TMP/ec.crt; ssl_certificate_key $TMP/ec.key;
    location = /scheme { return 200 "\$scheme\n"; }
  }
  server {
    listen 127.0.0.1:$TLSPORT ssl; server_name rsa.test;
    ssl_certificate $TMP/rsa.crt; ssl_certificate_key $TMP/rsa.key;
    return 200 "rsa\n";
  }
}
CONF
"$BIN" -t -c "$TMP/t.conf" 2>/dev/null || { echo "FAIL config test"; exit 1; }
"$BIN" -c "$TMP/t.conf" 2>"$TMP/err.log" & SRV=$!
i=0; until curl -s -o /dev/null "http://127.0.0.1:$PORT/health"; do i=$((i+1)); [ $i -gt 100 ] && { echo "server did not start"; cat "$TMP/err.log"; exit 1; }; sleep 0.05; done
sleep 0.3  # let the upstream start too
B="http://127.0.0.1:$PORT"
fail=0
check() { # name expected actual
  if [ "$2" = "$3" ]; then echo "ok   $1"; else echo "FAIL $1: expected [$2] got [$3]"; fail=1; fi
}
code() { curl -s -o /dev/null -w "%{http_code}" "$@"; }
raw()  { printf "$1" | nc -w 2 127.0.0.1 $PORT | head -1 | tr -d '\r' | cut -d' ' -f2; }
check "index"              200 "$(code $B/)"
check "file body"          "hello from leannginx" "$(curl -s $B/files/hello.txt)"
check "json mime"          "application/json" "$(curl -s -o /dev/null -w '%{content_type}' $B/files/data.json)"
check "autoindex"          200 "$(code $B/files/)"
check "dir redirect"       301 "$(code $B/files/sub%20dir)"
check "custom 404"         404 "$(code $B/nope)"
check "custom 404 body"    1 "$(curl -s $B/nope | grep -c 'error_page 404')"
check "return text"        "ok" "$(curl -s $B/health)"
check "return 410"         410 "$(code $B/gone)"
check "return 301"         301 "$(code $B/old/x)"
check "alias"              "hello from leannginx" "$(curl -s $B/img/hello.txt)"
check "alias traversal"    404 "$(code --path-as-is "$B/img../conf/nginx.conf")"
check "dotdot"             400 "$(code --path-as-is "$B/../../etc/passwd")"
check "encoded dotdot"     400 "$(code "$B/files/%2e%2e/%2e%2e/%2e%2e/etc/passwd")"
check "encoded NUL"        400 "$(code "$B/a%00b")"
check "double-encoded path" 404 "$(code --path-as-is "$B/%2566iles/hello.txt")"
check "double-encoded dotdot" 404 "$(code --path-as-is "$B/x/%252e%252e/files/hello.txt")"
check "range"              "from" "$(curl -s -r 6-9 $B/files/hello.txt)"
check "range 416"          416 "$(code -r 999- $B/files/hello.txt)"
ET=$(curl -s -I $B/files/hello.txt | tr -d '\r' | awk -F': ' 'tolower($1)=="etag"{print $2}')
check "etag 304"           304 "$(code -H "If-None-Match: $ET" $B/files/hello.txt)"
LM=$(curl -s -I $B/files/hello.txt | tr -d '\r' | awk -F': ' 'tolower($1)=="last-modified"{print $2}')
check "if-modified-since"  304 "$(code -H "If-Modified-Since: $LM" $B/files/hello.txt)"
check "HEAD no body"       0 "$(curl -s -I $B/ | sed '1,/^\r$/d' | wc -c | tr -d ' ')"
check "POST static 405"    405 "$(code -X POST -d a=1 $B/)"
check "413"                413 "$(head -c 2000000 /dev/zero | curl -s -o /dev/null -w '%{http_code}' -X POST --data-binary @- $B/)"
check "binary intact"      ok "$(curl -s $B/files/random.bin | cmp -s - html/files/random.bin && echo ok)"
check "proxy"              "from upstream" "$(curl -s $B/api/u.txt)"
check "vhost wildcard"     "vhost www.vhost.test" "$(curl -s -H 'Host: www.vhost.test' $B/)"
check "no Host 1.1"        400 "$(raw 'GET / HTTP/1.1\r\n\r\n')"
check "CL+TE"              411 "$(raw 'POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n')"
check "space before colon" 400 "$(raw 'GET / HTTP/1.1\r\nHost : a\r\n\r\n')"
check "HTTP/2.0"           505 "$(raw 'GET / HTTP/2.0\r\nHost: a\r\n\r\n')"
check "pipelining"         2 "$(printf 'GET /health HTTP/1.1\r\nHost: a\r\n\r\nGET /health HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n' | nc -w 2 127.0.0.1 $PORT | grep -c '^HTTP/1.1 200')"
check "keep-alive reuse"   "1 0 0" "$(curl -s -o /dev/null -o /dev/null -o /dev/null -w '%{num_connects} ' $B/ $B/health $B/files/hello.txt | sed 's/ $//')"
check "header too large"   431 "$(python3 -c "print('GET / HTTP/1.1\r\nHost: a\r\nX: ' + 'a'*40000 + '\r\n\r\n', end='')" | nc -w 2 127.0.0.1 $PORT | head -1 | cut -d' ' -f2)"
check "parallel x500"      "500" "$(seq 500 | xargs -P 50 -I{} curl -s -o /dev/null -w '%{http_code}\n' $B/files/random.bin | grep -c 200)"
T="https://localhost:$TLSPORT"
check "https file"         "hello from leannginx" "$(curl -s --cacert "$TMP/ec.crt" $T/files/hello.txt)"
check "https scheme"       "https" "$(curl -s --cacert "$TMP/ec.crt" $T/scheme)"
check "https SNI + RSA"    "rsa" "$(curl -s --cacert "$TMP/rsa.crt" --resolve rsa.test:$TLSPORT:127.0.0.1 https://rsa.test:$TLSPORT/)"
check "https TLS 1.3"      "TLSv1.3" "$(echo | openssl s_client -connect 127.0.0.1:$TLSPORT -servername localhost 2>/dev/null | awk '/^ *Protocol *:/{print $NF; exit}')"
check "https P-256 share"  0 "$(echo | openssl s_client -connect 127.0.0.1:$TLSPORT -servername localhost -groups P-256 >/dev/null 2>&1; echo $?)"
check "https rejects 1.2"  1 "$(echo | openssl s_client -connect 127.0.0.1:$TLSPORT -tls1_2 2>&1 | grep -c 'alert protocol version')"
check "https binary"       ok "$(curl -s --cacert "$TMP/ec.crt" $T/files/random.bin | cmp -s - html/files/random.bin && echo ok)"
check "https keep-alive"   "1 0" "$(curl -s --cacert "$TMP/ec.crt" -o /dev/null -o /dev/null -w '%{num_connects} ' $T/ $T/files/data.json | sed 's/ $//')"
check "plain HTTP on TLS"  400 "$(code http://127.0.0.1:$TLSPORT/)"
check "gzip encoding"      gzip "$(curl -s -o /dev/null -D - -H 'Accept-Encoding: gzip' $B/gz/page.html | tr -d '\r' | awk -F': ' 'tolower($1)=="content-encoding"{print $2}')"
check "gzip roundtrip"     ok "$(curl -s --compressed $B/gz/page.html | cmp -s - "$TMP/page.html" && echo ok)"
check "gzip off by default" "" "$(curl -s -o /dev/null -D - -H 'Accept-Encoding: gzip' $B/files/hello.txt | grep -i content-encoding)"
check "gzip not for ranges" "" "$(curl -s -o /dev/null -D - -r 0-5 -H 'Accept-Encoding: gzip' $B/gz/page.html | grep -i content-encoding)"
check "regex location"     "regex" "$(curl -s $B/a/b/C.JPG)"
check "^~ beats regex"     "noregex" "$(curl -s $B/pics/x.gif)"
check "auth required"      401 "$(code $B/private/u.txt)"
check "auth ok"            "from upstream" "$(curl -s -u smoke:hunter2 $B/private/u.txt)"
check "auth wrong password" 401 "$(code -u smoke:hunter3 $B/private/u.txt)"
# a 16 kB password must be refused at once, not hashed (SHA-256-crypt is quadratic in its length)
check "auth huge password" 401 "$(code -m 5 -u "smoke:$(head -c 16000 /dev/zero | tr '\0' a)" $B/private/u.txt)"
check "try_files via own location" "games" "$(curl -s "$B/cat?games")"
check "try_files no auth bypass" 401 "$(code --path-as-is "$B/cat?../secret/s")"
check "try_files bypass, creds"  "secret page" "$(curl -s -u smoke:hunter2 --path-as-is "$B/cat?../secret/s")"
check "names are case-exact"     404 "$(code "$B/SECRET/s.html")"
check "autoindex link encoded"   1 "$(curl -s $B/ls/ | grep -c 'href="javascript%3Aalert(1)"')"
check "proxy refuses ..;"         400 "$(code --path-as-is "$B/api/..;/x")"
check "proxy sends routed path"  "from upstream" "$(curl -s --path-as-is "$B/files/..%2Fapi/u.txt")"
# RFC MUST + fail-loud fixes
ALLOW=$(raw 'POST / HTTP/1.1\r\nHost: a\r\n\r\n'; printf '' )
check "405 has Allow"          1   "$(printf 'POST /files/hello.txt HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n' | nc -w 2 127.0.0.1 $PORT | tr -d '\r' | grep -ic '^Allow: GET, HEAD$')"
check "no 100 to HTTP/1.0"     0   "$(printf 'POST /files/hello.txt HTTP/1.0\r\nHost: a\r\nExpect: 100-continue\r\nContent-Length: 3\r\n\r\nabc' | nc -w 2 127.0.0.1 $PORT | grep -c '100 Continue')"
check "100 to HTTP/1.1"        1   "$(printf 'POST /files/hello.txt HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nContent-Length: 3\r\n\r\n' | nc -w 2 127.0.0.1 $PORT | grep -c '100 Continue')"
# -t must reject security-relevant unsupported directives
rejconf() { printf 'http{server{listen 127.0.0.1:%d;%s}}\n' "$PORT" "$1" > "$TMP/rej.conf"; "$BIN" -t -c "$TMP/rej.conf" >/dev/null 2>&1; echo $?; }
check "reject proxy_set_header" 1 "$(rejconf 'proxy_set_header X-Forwarded-For "";')"
check "reject user"            1 "$(printf 'user nginx;\nhttp{server{listen 127.0.0.1:%d;}}\n' "$PORT" > "$TMP/rej.conf"; "$BIN" -t -c "$TMP/rej.conf" >/dev/null 2>&1; echo $?)"
check "reject add_header always" 1 "$(rejconf 'add_header X-Frame-Options DENY always;')"
check "accept add_header (2-arg)" 0 "$(rejconf 'add_header X-Frame-Options DENY;')"
check "access log"         1 "$(grep -c '"GET /files/hello.txt HTTP/1.1" 200 21' "$TMP/access.log" | awk '{print ($1>0)}')"
[ $fail = 0 ] && echo "all smoke checks passed" || { echo "some smoke checks FAILED"; exit 1; }
