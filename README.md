# leannginx

A web server that reads **nginx configuration files**, written in Lean 4 and compiled to native
code through C. You can run it locally to serve a directory of pages. Its request handling is
specified by theorems that `lake build` checks: header parsing, path normalisation, location
matching, and the mapping from URLs to files.

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
# needs elan (https://github.com/leanprover/elan); Lean 4.36.0 is pinned and installed on first build
git clone https://github.com/Beneficial-AI-Foundation/leannginx && cd leannginx
lake build                 # checks every proof and spec (seconds), no binary
lake build lnginx          # builds the server: .lake/build/bin/lnginx
.lake/build/bin/lnginx     # serves ./html on http://127.0.0.1:8080/ using ./conf/nginx.conf
```

Then open <http://127.0.0.1:8080/>. Stop it with Ctrl-C. Requests are logged to
`logs/access.log` in nginx's `combined` format.

### Serve your own site

```sh
lnginx -t                          # test the configuration, like nginx -t
lnginx -p /path/to/prefix          # prefix: relative root/alias/access_log/conf paths start here
lnginx -c /path/to/site.conf       # use another configuration file
lnginx -V                          # version and what is verified
```

A minimal configuration:

```nginx
http {
    include mime.types;              # relative to the configuration file's directory
    server {
        listen 127.0.0.1:8000;
        root   /Users/me/www;
        location / { try_files $uri $uri/ /index.html; }   # single-page app
        location /api/ { proxy_pass http://127.0.0.1:3000/; }
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
| `server` | `listen` (`port`, `addr:port`, `[v6]:port`, `default_server`), `server_name` (exact, `*.example.com`, `.example.com`), `location`, `return` |
| `location` | `=` exact, `^~`, prefix; nginx's matching order (exact, then longest prefix). `root`, `alias`, `index`, `autoindex`, `try_files` (incl. `=404`, `$uri/`, fallback URI), `return code [text\|URL]` (incl. `444`), `proxy_pass http://…`, `add_header`, `error_page` |
| Variables | `$uri`, `$document_uri`, `$request_uri`, `$args`, `$query_string`, `$is_args`, `$host`, `$server_name`, `$request_method`, `$remote_addr`, `$server_port`, `$scheme`, also as `${name}` |
| HTTP | HTTP/1.0 and 1.1, keep-alive, pipelining, `Expect: 100-continue`, `HEAD`, absolute-form targets, `405` for non-GET on static files |
| Static files | MIME types, `Last-Modified`, nginx-format `ETag`, `If-None-Match`, `If-Modified-Since`, single byte ranges (`206`/`416`, `If-Range`), streaming of large files |
| Errors | nginx's built-in error pages; `error_page` internal redirects (keeping the status code); at most 10 internal redirects |
| Proxy | `proxy_pass http://host[:port][/uri]` with DNS, nginx's URI replacement rule, hop-by-hop header removal, `502`/`504` |

Directives that only tune nginx internals (`sendfile`, `tcp_nopush`, hash sizes, timeouts, …)
are accepted silently. Ones whose absence changes responses (`gzip`, `expires`, `charset`,
`proxy_set_header`, `log_format`, …) are accepted with a warning.

## How it is built

```
LeanNginx/Bytes.lean     byte strings, `b!"…"` literals
LeanNginx/Uri.lean       percent-decoding, path normalisation  ─┐
LeanNginx/Http.lean      request-head parser (RFC 9112)         │ pure, specified
LeanNginx/Config.lean    nginx.conf lexer, parser, elaborator   │
LeanNginx/Route.lean     server/location selection, routing     │
LeanNginx/Response.lean  headers, error pages, ranges, dates   ─┘
LeanNginx/Proofs/        supporting lemmas
LeanNginx/Spec.lean      the specification (the test suite)
LeanNginx/Audit.lean     generated axiom audit of every spec
Main.lean                IO shell: sockets, files, clock, logs (not specified)
```

Routing needs to know which files exist, but the router is pure: `route` returns a small
program (`Step`) that asks `stat` questions. `Main.lean` answers them with real `stat` calls;
the specs quantify over *all* possible answers, so they hold whatever is on disk.

Networking uses Lean's built-in `Std.Async` (libuv). There is no hand-written C: the only C is
what the Lean compiler generates.

## What's proved

All in [`LeanNginx/Spec.lean`](LeanNginx/Spec.lean); 52 theorems, each pinned by the axiom
audit (`propext`, `Classical.choice`, `Quot.sound` only — no `sorry`, no `native_decide`).

**For all inputs:**

- *Request parsing:* accepted methods are tokens; header names are tokens and values contain no
  NUL/CR/LF (`parseRequest_values_no_crlf`); `Transfer-Encoding` is never accepted, and every
  `Content-Length` agrees with the length used (`parseRequest_no_transfer_encoding`,
  `parseRequest_content_length`), which rules out CL/TE request smuggling; the host contains no
  `/`, CR, LF, quotes or `<`.
- *Paths:* every segment of a normalised path is safe (`normalizePath_segments_safe`);
  percent-decoding inverts percent-encoding; encoded output has no CR/LF/space/quotes/`<>`.
- *Locations:* the selected location matches; an exact match always wins; otherwise no matching
  prefix is longer (`selectLocation_sound`, `_exact`, `_longest`). The selected server listens
  on the request's port.
- *Confinement:* `route_confined` / `route_serves_under` (above).
- *Responses:* header names and values written to the wire contain no CR/LF
  (`renderHead_values_safe`), autoindex text is HTML-escaped, byte ranges lie inside the file
  and `Content-Length` equals the bytes sent (`fileResponse_body_in_file`).

**Concrete vectors** (kernel-checked): request heads (minimal GET, missing Host, CL+TE, duplicate
CL, `Host :`, obs-fold, NUL, HTTP/2.0, bad hosts, absolute-form), URI normalisation (`.`/`..`,
encoded traversal, `%00`, `%2F`), the location example from nginx's documentation, end-to-end
routing on a test server and file system (index, 301 for directories, autoindex, `return`,
404, 405, `alias`, the alias traversal), byte ranges, the RFC 9110 date example, ETags, server
names, variables, config lexing/parsing, `listen` and size/time arguments.

**Not covered by specs:** `Main.lean` (sockets, file reads, logs, the proxy's byte relay).
`scripts/smoke.sh` checks it end to end (34 checks, including hostile requests and 500
parallel downloads).

```sh
./audit.sh            # regenerate LeanNginx/Audit.lean after changing specs
scripts/smoke.sh      # end-to-end check of the built binary
```

## Performance

On an Apple-silicon laptop, `hey -n 20000 -c 50` against the start page: about 9,700 requests/s
with keep-alive and no errors, around 15 MB resident. A 200 MB file streams intact, and ranges
deep inside it are byte-exact.

## Not done yet

- **TLS** (`listen … ssl`): rejected at config time. The sibling project
  [leantls](https://github.com/Beneficial-AI-Foundation/leantls) has a TLS 1.3 *client*; a server
  side would be the next step.
- Regex locations (`~`, `~*`), named locations (`@name`), nested locations, `rewrite`, `if`,
  `map`, `upstream` blocks, `gzip`, `expires`, custom `log_format`: rejected or ignored with a
  message.
- Request bodies with `Transfer-Encoding: chunked` get `411 Length Required`.
- `proxy_pass` speaks HTTP/1.0 to the upstream, does not support `https://` upstreams or
  WebSockets, and closes the client connection after a proxied response.
- Multipart byte ranges (several ranges in one request) are answered with the whole file, which
  RFC 9110 allows.
- `alias` deliberately differs from nginx in one case: with `location /img { alias /data/img; }`,
  `/imgx/a` maps to `/data/img/x/a` (always inside the alias directory), not `/data/imgx/a`.
- Symlinks are followed, as in nginx's default (`disable_symlinks off`).

## License

MIT. `conf/mime.types` lists the common types from nginx's file of the same name.
