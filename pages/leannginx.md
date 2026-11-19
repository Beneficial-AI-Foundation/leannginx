# leannginx: an nginx-compatible web server, written in Lean and proved

leannginx reads nginx configuration files and serves web pages. It is written in Lean 4 and compiled to native code through C. Every decision it makes about a request (whether the request is well formed, which `server` and `location` handle it, and which file on disk answers it) is made by pure Lean code that `lake build` checks against a specification.

```stats
{
  "items": [
    { "value": "52", "label": "Specs checked by lake build", "hint": "no sorry, no native_decide" },
    { "value": "0", "label": "Lines of hand-written C", "hint": "sockets via Lean's Std.Async" },
    { "value": "34", "label": "End-to-end checks", "hint": "scripts/smoke.sh, incl. hostile requests" },
    { "value": "~9.7k", "label": "Requests per second", "hint": "keep-alive, 50 clients, laptop" }
  ]
}
```

```cards
{
  "repos": ["OWNER/leannginx"],
  "variant": "green"
}
```

## The main theorem

nginx maps a URL to a file by appending the request path to a `root` or `alias` directory. Getting that wrong is a classic source of path traversal. nginx itself is safe, but a common configuration mistake is not: `location /img { alias /data/img/; }` lets `GET /img../secret` read `/data/secret`.

In leannginx the router is a pure function that returns a small program of `stat` questions; the server answers them with real `stat` calls. The specification quantifies over every possible answer, so it holds whatever is on disk:

```latex
\forall\, \mathit{cfg}, \mathit{req}, \mathit{fs}:\quad
\mathrm{path}(\mathrm{route}(\mathit{cfg}, \mathit{req}, \mathit{fs})) =
\mathit{base}(\ell) \,/\, s_1 / \cdots / s_n,
\qquad s_i \notin \{\varepsilon, \texttt{.}, \texttt{..}\},\ \texttt{/} \notin s_i
```

where ℓ is the location the request matched and base(ℓ) is its `alias`, or else its effective `root`. This is `LeanNginx.Spec.route_confined`. The `/img..` request from above finds nothing (`vector_alias`).

## What is proven

**For all inputs:**

- **Request heads (RFC 9112).** Methods and header names are tokens; header values contain no NUL, CR or LF, so they cannot inject headers anywhere they are copied. `Transfer-Encoding` is never accepted and every `Content-Length` agrees with the length used, which rules out CL/TE request smuggling. Hosts contain no `/`, quotes or angle brackets.
- **Paths.** Every segment of a normalised path is safe, whatever the client sent, percent-encoded or not. Percent-decoding inverts percent-encoding, and encoded output contains no CR, LF, space, quote or `<>`.
- **Locations.** The selected location matches the URI; an exact `=` location always wins; otherwise no matching prefix is longer than the one chosen. The selected `server` listens on the port the request arrived on.
- **Responses.** Header names and values written to the wire contain no CR or LF; autoindex names are HTML-escaped; byte ranges lie inside the file and `Content-Length` equals the number of bytes sent.

**Concrete vectors**, checked by the kernel: malformed and hostile request heads, URI normalisation including encoded traversal and `%00`, the `location` example from the nginx documentation, end-to-end routing on a test server and file system (index files, directory redirects, autoindex, `return`, 404, 405, `alias`), byte ranges, the RFC 9110 date example, ETags, server names, variables and configuration parsing.

## What it does

It reads `nginx.conf` with `include`, `server`, `listen`, `server_name` (exact and wildcard), `location` (`=`, `^~`, prefix), `root`, `alias`, `index`, `autoindex`, `try_files`, `return`, `error_page`, `add_header` and `proxy_pass`, and the usual variables (`$uri`, `$host`, `$args`, …). It speaks HTTP/1.0 and 1.1 with keep-alive and pipelining, supports conditional requests (`ETag`, `If-Modified-Since`) and byte ranges, and writes nginx's `combined` access log. `lnginx -t` tests a configuration with nginx-style error messages.

## What the code is made of

```chart
{
  "id": "leannginx-lines",
  "type": "stacked-bar",
  "title": "Lines of Lean",
  "width": "full",
  "height": 260,
  "x": { "type": "category", "field": "part" },
  "legend": { "show": false },
  "series": [ { "key": "lines", "label": "Lines", "color": "#217ef0" } ],
  "source": { "kind": "inline" },
  "data": [
    { "part": "Program (pure)", "lines": 1313 },
    { "part": "IO shell", "lines": 564 },
    { "part": "Specs", "lines": 454 },
    { "part": "Proofs", "lines": 481 }
  ]
}
```

The pure program parses, routes and builds responses. The IO shell, `Main.lean`, only moves bytes: sockets, file reads, the clock and logs.

## What you still have to trust

- **The Lean kernel**, which checks the proofs.
- **The Lean compiler, the C compiler, the runtime and libuv** (under `Std.Async`).
- **`Main.lean`**, which is not specified. `scripts/smoke.sh` checks it end to end with 34 requests, including hostile ones and 500 parallel downloads.
- **The file system.** Symbolic links are followed, as in nginx's default.

## Not built

- TLS (`listen … ssl` is rejected), regex and named locations, `rewrite`, `if`, `map`, `upstream` blocks, gzip.
- Request bodies with `Transfer-Encoding: chunked` get `411 Length Required`.
- `proxy_pass` speaks HTTP/1.0 to the upstream and closes the client connection after a proxied response.

Source: [github.com/Beneficial-AI-Foundation/leannginx](https://github.com/Beneficial-AI-Foundation/leannginx)
