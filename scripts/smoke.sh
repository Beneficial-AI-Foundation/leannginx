#!/bin/sh
# End-to-end smoke check of a built lnginx binary against the sample site in ./html.
# Not where correctness comes from (that is LeanNginx/Spec.lean); it checks the IO shell.
# Usage: scripts/smoke.sh [path/to/lnginx]
set -u
cd "$(dirname "$0")/.."
BIN=${1:-.lake/build/bin/lnginx}
PORT=18089
UP=18090
TMP=$(mktemp -d)
trap 'kill $SRV $UPS 2>/dev/null; rm -rf "$TMP"' EXIT
mkdir -p "$TMP/up" && echo "from upstream" > "$TMP/up/u.txt"
[ -f html/files/random.bin ] || head -c 300000 /dev/urandom > html/files/random.bin
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
    location /old/ { return 301 /; }
    error_page 404 /404.html;
  }
  server { listen 127.0.0.1:$PORT; server_name *.vhost.test; return 200 "vhost \$host\n"; }
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
check "access log"         1 "$(grep -c '"GET /files/hello.txt HTTP/1.1" 200 21' "$TMP/access.log" | awk '{print ($1>0)}')"
[ $fail = 0 ] && echo "all smoke checks passed" || { echo "some smoke checks FAILED"; exit 1; }
