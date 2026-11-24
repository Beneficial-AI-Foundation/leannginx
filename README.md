# leannginx

A web server that reads **nginx configuration files**, written in Lean 4 and compiled to native
code through C. You can run it locally to serve a directory of pages, over HTTP or HTTPS. Its
request handling is specified by theorems that `lake build` checks: header parsing, path
normalisation, location matching (including regex locations), and the mapping from URLs to files.

It is built on two other verified Lean libraries:

- [LeanTLS](https://github.com/Beneficial-AI-Foundation/leantls) for HTTPS (TLS 1.3; its server
  side was written for leannginx),
- [lean-zip](https://github.com/kim-em/lean-zip) for gzip (a DEFLATE implementation whose
  `decompress (compress x) = x` is a theorem).

The headline guarantee (`route_confined` in [`LeanNginx/Spec.lean`](LeanNginx/Spec.lean)):

> For **every** configuration, **every** request and **every** state of the file system, every
> path the server `stat`s, serves or lists is the matched location's `root`/`alias` directory
> followed by *safe* segments (never empty, `.`, `..`, never containing `/` or NUL).

That excludes path traversal, including nginx's well-known `alias` off-by-slash bug
(`location /img { alias /data/img/; }` + `GET /img../secret`).

> ⚠ **Research code.** It is meant for local development and demos, not as an internet-facing
> replacement for nginx. See [Not done yet](#not-done-yet).

## Quick start

```sh
# needs elan (https://github.com/leanprover/elan); Lean 4.35.0 is pinned and installed on first build
git clone https://github.com/Beneficial-AI-Foundation/leannginx && cd leannginx
lake build                 # checks every proof and spec, no binary (first time ≈5 min: lean-zip's proofs)
lake build lnginx          # builds the server: .lake/build/bin/lnginx
.lake/build/bin/lnginx     # serves ./html on http://127.0.0.1:8080/ using ./conf/nginx.conf
```

Then open <http://127.0.0.1:8080/>. Stop it with Ctrl-C. Requests are logged to
`logs/access.log` in nginx's `combined` format.

### HTTPS

```sh
scripts/gen-cert.sh        # self-signed ECDSA certificate for localhost in conf/
# uncomment the HTTPS server at the end of conf/nginx.conf, restart, open https://localhost:8443/
```

Browsers warn about a self-signed certificate. With [mkcert](https://github.com/FiloSottile/mkcert)
you get one your browser trusts:
`mkcert -ecdsa -cert-file conf/localhost.crt -key-file conf/localhost.key localhost 127.0.0.1`.
RSA certificates work too.

### Serve your own site

```sh
lnginx -t                          # test the configuration, like nginx -t
lnginx -p /path/to/prefix          # prefix: relative root/alias/access_log paths start here
lnginx -c /path/to/site.conf       # use another configuration file
lnginx -V                          # version and what is verified
```

A configuration:

```nginx
http {
    include mime.types;              # relative to the configuration file's directory
    gzip on;
    gzip_types text/css application/javascript application/json;

    server {
        listen 127.0.0.1:8000;
        listen 127.0.0.1:8443 ssl;
        ssl_certificate     localhost.crt;
        ssl_certificate_key localhost.key;

        root /Users/me/www;
        location / { try_files $uri $uri/ /index.html; }           # single-page app
        location /api/ { proxy_pass http://127.0.0.1:3000/; }
        location ~* \.(png|jpe?g|gif|svg)$ { add_header Cache-Control "max-age=86400"; }
    }
}
```

To install it, copy the binary somewhere on your `PATH`, for example
`cp .lake/build/bin/lnginx ~/.local/bin/`. It has no runtime dependencies.

## What works

| Area | Supported |
|---|---|
| Syntax | nginx block syntax, `#` comments, quoted strings, `include` (with `*` globs), `nginx -t`-style errors (`unknown directive`, `invalid number of arguments`, …) |
| Main / events | accepted (`worker_processes`, `events { … }`, `user`, `pid`, …); one process serves all connections with Lean tasks |
| `http` | `server`, `types`, `include`, `default_type`, `access_log` (path or `off`), `keepalive_timeout`, `server_tokens`, `client_max_body_size`, plus everything inheritable below |
| `server` | `listen` (`port`, `addr:port`, `[v6]:port`, `default_server`, `ssl`), `server_name` (exact, `*.example.com`, `.example.com`), `location`, `return` |
| `location` | `=` exact, `^~`, prefix, `~` and `~*` regex; nginx's order (exact, longest prefix, first matching regex unless the prefix is `^~`). `root`, `alias`, `index`, `autoindex`, `try_files` (incl. `=404`, `$uri/`, fallback URI), `return code [text\|URL]` (incl. `444`), `proxy_pass http://…`, `add_header`, `error_page` |
| HTTPS | `listen … ssl`, `ssl_certificate`, `ssl_certificate_key` (ECDSA P-256 or RSA, PEM), SNI picks the server's certificate, TLS 1.3 with ChaCha20-Poly1305 and X25519/P-256, `$scheme`, nginx's 400 for plain HTTP on a TLS port. `ssl_protocols`, `ssl_ciphers`, `ssl_session_*` are accepted and ignored |
| gzip | `gzip`, `gzip_types` (`text/html` always, `*` for all), `gzip_min_length`, `gzip_comp_level`, `gzip_vary`; weak ETags for compressed responses, never for ranges |
| Regex | literals, `.`, `[…]`, `[^…]`, `\d \w \s \D \W \S`, groups, `(?:…)`, `\|`, `* + ? {n} {n,} {n,m}`, `^`, `$`; `~*` folds ASCII case |
| Variables | `$uri`, `$document_uri`, `$request_uri`, `$args`, `$query_string`, `$is_args`, `$host`, `$server_name`, `$request_method`, `$remote_addr`, `$server_port`, `$scheme`, also as `${name}` |
| HTTP | HTTP/1.0 and 1.1, keep-alive, pipelining, `Expect: 100-continue`, `HEAD`, absolute-form targets, `405` for non-GET on static files |
| Static files | MIME types, `Last-Modified`, nginx-format `ETag`, `If-None-Match`, `If-Modified-Since`, single byte ranges (`206`/`416`, `If-Range`), streaming of large files |
| Errors | nginx's built-in error pages; `error_page` internal redirects (keeping the status code); at most 10 internal redirects |
| Proxy | `proxy_pass http://host[:port][/uri]` with DNS, nginx's URI replacement rule, hop-by-hop header removal, `502`/`504` |

Directives that only tune nginx internals (`sendfile`, `tcp_nopush`, hash sizes, timeouts, …)
are accepted silently. Ones whose absence changes responses (`expires`, `charset`,
`proxy_set_header`, `log_format`, `gzip_proxied`, …) are accepted with a warning.

## How it is built

```
LeanNginx/Bytes.lean     byte strings, `b!"…"` literals
LeanNginx/Uri.lean       percent-decoding, path normalisation  ─┐
LeanNginx/Http.lean      request-head parser (RFC 9112)         │
LeanNginx/Regex.lean     regex parser, derivative matcher       │ pure, specified
LeanNginx/Config.lean    nginx.conf lexer, parser, elaborator   │
LeanNginx/Route.lean     server/location selection, routing     │
LeanNginx/Response.lean  headers, error pages, ranges, gzip    ─┘
LeanNginx/Proofs/        supporting lemmas
LeanNginx/Spec.lean      the specification (the test suite)
LeanNginx/Audit.lean     generated axiom audit of every spec
Main.lean                IO shell: sockets, TLS, files, clock, logs (not specified)
```

Routing needs to know which files exist, but the router is pure: `route` returns a small
program (`Step`) that asks `stat` questions. `Main.lean` answers them with real `stat` calls;
the specs quantify over *all* possible answers, so they hold whatever is on disk.

Networking uses Lean's built-in `Std.Async` (libuv). leannginx and LeanTLS contain no
hand-written C. lean-zip ships four small C primitives (fast byte copies), each with a pure-Lean
reference and a proof that they agree.

The Lean version is 4.35.0 because that is what lean-zip's pinned commit builds with. When you
update dependencies, use `lake update --keep-toolchain`, or Lake will move to LeanTLS's newer
toolchain, which lean-zip does not build with yet.

## What's proved

All in [`LeanNginx/Spec.lean`](LeanNginx/Spec.lean): 65 theorems, each pinned by the axiom audit.
They use only `propext`, `Classical.choice` and `Quot.sound` (no `sorry`, no `native_decide`),
except `gzip_roundtrip`, which is lean-zip's theorem and also trusts the compiled checker that
`bv_decide` uses.

**For all inputs:**

- *Request parsing:* accepted methods are tokens; header names are tokens and values contain no
  NUL/CR/LF (`parseRequest_values_no_crlf`); `Transfer-Encoding` is never accepted, and every
  `Content-Length` agrees with the length used (`parseRequest_no_transfer_encoding`,
  `parseRequest_content_length`), which rules out CL/TE request smuggling; the host contains no
  `/`, CR, LF, quotes or `<`.
- *Paths:* every segment of a normalised path is safe (`normalizePath_segments_safe`);
  percent-decoding inverts percent-encoding; encoded output has no CR/LF/space/quotes/`<>`.
- *Regex:* the matcher accepts a URI exactly when the URI is in the regex's language
  (`regexMatches_iff`, against the textbook inductive definition). It works by derivatives, so it
  never backtracks.
- *Locations:* the selected location matches; an exact match always wins; a selected prefix
  location is the longest matching one; a selected regex location is the first matching one in
  configuration order; a plain prefix is selected only if no regex matches
  (`selectLocation_sound`, `_exact`, `_longest`, `_regex`, `_prefix_no_regex`). The selected
  server listens on the request's port.
- *Confinement:* `route_confined` / `route_serves_under` (above).
- *Responses:* header names and values written to the wire contain no CR/LF
  (`renderHead_values_safe`), autoindex text is HTML-escaped, byte ranges lie inside the file
  and `Content-Length` equals the bytes sent (`fileResponse_body_in_file`).
- *gzip:* decompressing what the server sends returns the file (`gzip_roundtrip`); compression is
  used only for clients that accept it and never for range requests (`gzipApplies_requires`).
- *Basic auth:* only a user from the user file with a matching password passes
  (`basicOk_sound`), and a 401 comes before any file is looked at (`routeAuth_denied`). A password
  longer than 511 bytes never matches and is not hashed (`verifyCrypt_long_password`), which
  bounds the work one request can ask for (`cryptWork_bounded`).

**In LeanTLS** (`LeanTLS/Spec/Server.lean`, kernel-checked): the server accepts only TLS 1.3,
ChaCha20-Poly1305, a signature scheme the client offered and a well-formed key share it sent;
ECDSA signing reproduces the RFC 6979 vector; the client's and server's hello messages parse with
each other's parser; a loaded certificate and key always belong together.

**Concrete vectors** (kernel-checked): request heads (minimal GET, missing Host, CL+TE, duplicate
CL, `Host :`, obs-fold, NUL, HTTP/2.0, bad hosts, absolute-form), URI normalisation (`.`/`..`,
encoded traversal, `%00`, `%2F`), the full `location` example from nginx's documentation
(A–E, including the `~*` regex), regex syntax and its error cases, end-to-end routing on a test
server and file system (index, 301 for directories, autoindex, `return`, 404, 405, `alias`, the
alias traversal), byte ranges, `Accept-Encoding` and `gzip_types`, the RFC 9110 date example,
ETags, server names, variables, config lexing/parsing, `listen` and size/time arguments.

**Not covered by specs:** `Main.lean` (sockets, file reads, logs, the proxy's byte relay) and the
TLS connection loop in `LeanTLS/Server.lean`. `scripts/smoke.sh` checks them end to end
(49 checks, including hostile requests, HTTPS with ECDSA and RSA certificates, SNI, a TLS 1.2
client being refused, gzip and regex locations).

```sh
./audit.sh            # regenerate LeanNginx/Audit.lean after changing specs
scripts/smoke.sh      # end-to-end check of the built binary
```

## Performance

Against nginx 1.31.9 on the same 14-core Apple-silicon laptop: same files and configuration,
access logs off, keep-alive, best of two alternating rounds (`hey`). Requests per second unless
noted.

| Scenario | leannginx | nginx, 1 worker | nginx, 14 workers |
|---|---:|---:|---:|
| `return 200` | 23,435 | 107,474 | 106,343 |
| 628 B file | 17,494 | 38,150 | 42,171 |
| 129 KB page | **9,674** | 5,219 | 11,387 |
| 129 KB page with gzip | **12,256** | 5,291 | 31,386 |
| gzip output for that page | **17,554 B** | 19,072 B | 19,072 B |
| HTTPS `return 200` | 7,836 | 88,366 | 73,589 |
| HTTPS, new connection per request | 1,398 | 6,699 | 7,504 |
| HTTP, one 200 MB file | 3.7 GB/s | 10.4 GB/s | 10.2 GB/s |
| HTTPS, one 50 MB file | 28.7 MB/s | 537 MB/s | 541 MB/s |

Where the time goes, and what was done about it:

- **One event loop.** Lean's `Std.Async` runs all socket I/O through one libuv loop, and its TCP
  sockets cannot share a port between processes (no `SO_REUSEPORT`), so nginx's one-process-per-core
  model is not available. Throughput is nearly flat from 1 to 14 threads. Each request therefore
  keeps its loop operations to a minimum: reads have no timer of their own (a once-a-second
  watchdog cancels overdue reads), small files go out in one write, and the `Date` header is
  formatted once a second.
- **Small-file cache.** Small files and their gzip encodings are kept in memory, keyed by path,
  size and mtime from the `stat` the router does anyway, so a changed file is never served stale.
- **Poly1305.** The MAC runs a 26-bit-limb implementation in LeanTLS that is about 50x faster than
  the arbitrary-precision specification and is proved equal to it for every key and message
  (`Poly1305.macFast_eq`, used through `@[csimp]`). HTTPS bulk transfer went from 5.7 to 28.7 MB/s.
  ChaCha20 and the handshake arithmetic (X25519, P-256) are the next candidates for the same
  treatment.

## Not done yet

- HTTPS: no HelloRetryRequest (clients that send neither an X25519 nor a P-256 key share fail),
  no AES-GCM, no session resumption, no HTTP/2. Bulk TLS throughput is low (see above).
- Regex captures (`$1`), so `alias` inside a regex location is rejected; named locations
  (`@name`), nested locations, `rewrite`, `if`, `map`, `upstream` blocks, `expires`, custom
  `log_format`.
- gzip applies to static files up to 16 MiB; proxied responses and autoindex pages are not
  compressed.
- Request bodies with `Transfer-Encoding: chunked` get `411 Length Required`.
- `proxy_pass` speaks HTTP/1.0 to the upstream, does not support `https://` upstreams or
  WebSockets, and closes the client connection after a proxied response.
- Multipart byte ranges (several ranges in one request) are answered with the whole file, which
  RFC 9110 allows.
- `alias` deliberately differs from nginx in one case: with `location /img { alias /data/img; }`,
  `/imgx/a` maps to `/data/img/x/a` (always inside the alias directory), not `/data/imgx/a`.
- Symlinks are followed, as in nginx's default (`disable_symlinks off`).
- `auth_basic` accepts SHA-256-crypt (`$5$`) hashes only, and passwords of up to 511 bytes (the
  limit of libxcrypt's `crypt`); longer ones get 401.

## License

MIT. `conf/mime.types` lists the common types from nginx's file of the same name.
