/*
  SO_REUSEPORT bind for Std.Async TCP servers: a stopgap until Lean has `Server.bindReusePort`
  (leanprover/lean4#16687). It is the runtime's own `lean_uv_tcp_bind` (src/runtime/uv/tcp.cpp)
  with the libuv flag UV_TCP_REUSEPORT instead of 0, so several worker processes can listen on
  the same port and the kernel spreads connections over them.

  It reaches into private runtime internals, so it is tied to one Lean version:
    - the layout of `lean_uv_tcp_socket_object` (v4.35: first field `uv_tcp_t* m_uv_tcp`; later
      versions embed the handle instead, see src/runtime/uv/tcp.h);
    - the event-loop lock `lean::event_loop_lock(&lean::global_ev)` and
      `lean::lean_socket_address_to_sockaddr_storage` (C++ symbols, reached by their mangled names);
    - libuv's `uv_tcp_open`/`uv_tcp_bind` (linked into every Lean program; no uv.h in the toolchain).
  The #error below stops the build on any other Lean version: re-check those, then bump it.
*/
#include <lean/lean.h>
#include <lean/version.h>

#if !(LEAN_VERSION_MAJOR == 4 && LEAN_VERSION_MINOR == 35)
#error "c/reuseport.c is written against the Lean v4.35 runtime internals; re-check them before using another version"
#endif

#define LNGINX_STR2(x) #x
#define LNGINX_STR(x) LNGINX_STR2(x)
#define LNGINX_CXX(sym) __asm__(LNGINX_STR(__USER_LABEL_PREFIX__) sym)

extern char lnginx_global_ev LNGINX_CXX("_ZN4lean9global_evE");
void lnginx_event_loop_lock(void *) LNGINX_CXX("_ZN4lean15event_loop_lockEPNS_12event_loop_tE");
void lnginx_event_loop_unlock(void *) LNGINX_CXX("_ZN4lean17event_loop_unlockEPNS_12event_loop_tE");
void lnginx_to_sockaddr(lean_object *, void *)
  LNGINX_CXX("_ZN4lean39lean_socket_address_to_sockaddr_storageEP11lean_objectP16sockaddr_storage");

lean_object * lean_decode_uv_error(int errnum, lean_object * fname);
int uv_tcp_open(void * handle, int sock);
int uv_tcp_bind(void * handle, const void * addr, unsigned int flags);

/* struct sockaddr_storage: 128 bytes, 8-aligned; the toolchain clang has no system headers
   (-nostdinc), so the few libc declarations needed are spelled out here */
typedef struct { _Alignas(8) unsigned char bytes[128]; } lnginx_sockaddr_storage;

/* v4.35 `lean_uv_tcp_socket_object` starts with `uv_tcp_t* m_uv_tcp` */
typedef struct { void * m_uv_tcp; } lnginx_tcp_socket_prefix;

#ifdef __linux__
/* The bundled libuv is 1.48 on Linux (UV_TCP_REUSEPORT arrived in 1.49), so the socket is made
   here with SO_REUSEPORT set and handed to libuv with uv_tcp_open; uv_tcp_bind then uses it. */
int socket(int domain, int type, int protocol);
int setsockopt(int fd, int level, int name, const void * value, unsigned int len);
int close(int fd);
int * __errno_location(void);
#define LNGINX_SOCK_STREAM 1
#define LNGINX_SOCK_CLOEXEC 02000000
#define LNGINX_SOL_SOCKET 1
#define LNGINX_SO_REUSEPORT 15

/* LeanNginx.bindReusePort (socket : @& Std.Internal.UV.TCP.Socket) (addr : @& SocketAddress) : IO Unit */
LEAN_EXPORT lean_obj_res lnginx_tcp_bind_reuseport(b_lean_obj_arg server, b_lean_obj_arg addr) {
    lnginx_tcp_socket_prefix * s = (lnginx_tcp_socket_prefix *)lean_get_external_data(server);
    lnginx_sockaddr_storage sa;
    lnginx_to_sockaddr(addr, &sa);
    unsigned short family = *(unsigned short *)sa.bytes; /* sa_family_t, first field on Linux */
    int fd = socket(family, LNGINX_SOCK_STREAM | LNGINX_SOCK_CLOEXEC, 0);
    if (fd < 0) return lean_io_result_mk_error(lean_decode_uv_error(-*__errno_location(), NULL));
    int one = 1;
    if (setsockopt(fd, LNGINX_SOL_SOCKET, LNGINX_SO_REUSEPORT, &one, sizeof one) < 0) {
        int e = *__errno_location(); close(fd);
        return lean_io_result_mk_error(lean_decode_uv_error(-e, NULL));
    }
    lnginx_event_loop_lock(&lnginx_global_ev);
    int r = uv_tcp_open(s->m_uv_tcp, fd);
    if (r == 0) r = uv_tcp_bind(s->m_uv_tcp, &sa, 0);
    lnginx_event_loop_unlock(&lnginx_global_ev);
    if (r < 0) return lean_io_result_mk_error(lean_decode_uv_error(r, NULL));
    return lean_io_result_mk_ok(lean_box(0));
}
#else
LEAN_EXPORT lean_obj_res lnginx_tcp_bind_reuseport(b_lean_obj_arg server, b_lean_obj_arg addr) {
    (void)server; (void)addr;
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("SO_REUSEPORT load balancing is only supported on Linux")));
}
#endif

/* ---------------------------------------------------------------------------------------------
   send_timeout: libuv (and so Std.Async) cannot cancel a pending write, and a client that stops
   reading leaves it pending forever. `lnginx_tcp_abort` makes the kernel fail it instead: it
   sets SO_LINGER {on, 0} (the eventual close sends RST and drops unsent data) and shuts the socket
   down both ways. The socket then polls writable, libuv's next write attempt fails with EPIPE,
   the write's promise resolves with an error and the connection task closes the socket as usual.
   The handle itself is left to the runtime (closing it here would close it twice). */
int uv_fileno(const void * handle, int * fd);
int setsockopt(int fd, int level, int name, const void * value, unsigned int len);
int shutdown(int fd, int how);
#ifdef __linux__
#define LNGINX_SOL_SOCKET_ 1
#define LNGINX_SO_LINGER 13
#else
#define LNGINX_SOL_SOCKET_ 0xffff
#define LNGINX_SO_LINGER 0x0080
#endif
typedef struct { int l_onoff; int l_linger; } lnginx_linger;

/* LeanNginx.abortSocket (socket : @& Std.Internal.UV.TCP.Socket) : IO Unit */
LEAN_EXPORT lean_obj_res lnginx_tcp_abort(b_lean_obj_arg sock) {
    lnginx_tcp_socket_prefix * s = (lnginx_tcp_socket_prefix *)lean_get_external_data(sock);
    lnginx_event_loop_lock(&lnginx_global_ev);
    int fd = -1;
    if (uv_fileno(s->m_uv_tcp, &fd) == 0 && fd >= 0) {
        lnginx_linger l = { 1, 0 };
        setsockopt(fd, LNGINX_SOL_SOCKET_, LNGINX_SO_LINGER, &l, sizeof l);
        shutdown(fd, 2 /* SHUT_RDWR */);
    }
    lnginx_event_loop_unlock(&lnginx_global_ev);
    return lean_io_result_mk_ok(lean_box(0));
}
