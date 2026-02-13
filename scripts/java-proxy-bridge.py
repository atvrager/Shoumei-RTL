#!/usr/bin/env python3
"""
java-proxy-bridge.py — Local HTTP proxy that forwards to an authenticated upstream proxy.

Java's built-in HTTP client can't handle proxy auth via env vars.
This script bridges the gap: it listens on localhost (no auth) and
forwards CONNECT tunnels + plain HTTP requests to the upstream proxy
with the required Proxy-Authorization header.

Usage:
    python3 scripts/java-proxy-bridge.py &
    export SBT_OPTS="-Dhttp.proxyHost=127.0.0.1 -Dhttp.proxyPort=18080 -Dhttps.proxyHost=127.0.0.1 -Dhttps.proxyPort=18080"
    sbt run
"""

import os
import sys
import socket
import threading
import base64
import signal
from urllib.parse import urlparse

LOCAL_PORT = int(os.environ.get("BRIDGE_PORT", "18080"))
BUFFER_SIZE = 65536


def get_upstream_proxy():
    """Parse upstream proxy from environment."""
    proxy_url = os.environ.get("https_proxy") or os.environ.get("HTTPS_PROXY") or ""
    if not proxy_url:
        print("ERROR: No https_proxy env var set", file=sys.stderr)
        sys.exit(1)

    parsed = urlparse(proxy_url)
    host = parsed.hostname
    port = parsed.port or 3128
    username = parsed.username or ""
    password = parsed.password or ""

    if username:
        creds = f"{username}:{password}"
        auth = base64.b64encode(creds.encode()).decode()
        proxy_auth_header = f"Basic {auth}"
    else:
        proxy_auth_header = None

    return host, port, proxy_auth_header


UPSTREAM_HOST, UPSTREAM_PORT, PROXY_AUTH = get_upstream_proxy()


def relay(src, dst, name=""):
    """Relay data between two sockets until one side closes."""
    try:
        while True:
            data = src.recv(BUFFER_SIZE)
            if not data:
                break
            dst.sendall(data)
    except (OSError, BrokenPipeError):
        pass
    finally:
        try:
            dst.shutdown(socket.SHUT_WR)
        except OSError:
            pass


def handle_client(client_sock, addr):
    """Handle one client connection."""
    try:
        # Read the initial request line + headers
        raw = b""
        while b"\r\n\r\n" not in raw:
            chunk = client_sock.recv(BUFFER_SIZE)
            if not chunk:
                client_sock.close()
                return
            raw += chunk

        header_end = raw.index(b"\r\n\r\n")
        header_block = raw[:header_end].decode("latin-1")
        body_remainder = raw[header_end + 4:]

        lines = header_block.split("\r\n")
        request_line = lines[0]
        method = request_line.split()[0].upper()

        # Connect to upstream proxy
        upstream = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        upstream.settimeout(30)
        upstream.connect((UPSTREAM_HOST, UPSTREAM_PORT))

        # Rebuild headers, injecting Proxy-Authorization
        new_lines = [request_line]
        for line in lines[1:]:
            lower = line.lower()
            if lower.startswith("proxy-authorization:"):
                continue  # Remove any existing proxy auth
            new_lines.append(line)

        if PROXY_AUTH:
            new_lines.insert(1, f"Proxy-Authorization: {PROXY_AUTH}")

        new_header = "\r\n".join(new_lines) + "\r\n\r\n"
        upstream.sendall(new_header.encode("latin-1"))

        if method == "CONNECT":
            # For CONNECT (HTTPS tunneling), read upstream response first
            resp = b""
            while b"\r\n\r\n" not in resp:
                chunk = upstream.recv(BUFFER_SIZE)
                if not chunk:
                    client_sock.close()
                    upstream.close()
                    return
                resp += chunk

            resp_line = resp.split(b"\r\n")[0].decode("latin-1")
            if "200" in resp_line:
                # Tell client the tunnel is established
                client_sock.sendall(b"HTTP/1.1 200 Connection Established\r\n\r\n")

                # Forward any remaining data from the upstream 200 response body
                resp_end = resp.index(b"\r\n\r\n") + 4
                leftover = resp[resp_end:]
                if leftover:
                    client_sock.sendall(leftover)

                # Forward any body data we already buffered from client
                if body_remainder:
                    upstream.sendall(body_remainder)

                # Bi-directional relay
                t1 = threading.Thread(target=relay, args=(client_sock, upstream, "c->u"), daemon=True)
                t2 = threading.Thread(target=relay, args=(upstream, client_sock, "u->c"), daemon=True)
                t1.start()
                t2.start()
                t1.join()
                t2.join()
            else:
                # Forward error response to client
                client_sock.sendall(resp)
        else:
            # Plain HTTP — forward body remainder and then relay
            if body_remainder:
                upstream.sendall(body_remainder)

            t1 = threading.Thread(target=relay, args=(client_sock, upstream, "c->u"), daemon=True)
            t2 = threading.Thread(target=relay, args=(upstream, client_sock, "u->c"), daemon=True)
            t1.start()
            t2.start()
            t1.join()
            t2.join()

    except Exception as e:
        print(f"  error handling {addr}: {e}", file=sys.stderr)
    finally:
        try:
            client_sock.close()
        except OSError:
            pass
        try:
            upstream.close()
        except OSError:
            pass


def main():
    signal.signal(signal.SIGCHLD, signal.SIG_IGN)

    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("127.0.0.1", LOCAL_PORT))
    server.listen(64)

    print(f"java-proxy-bridge listening on 127.0.0.1:{LOCAL_PORT}")
    print(f"  upstream: {UPSTREAM_HOST}:{UPSTREAM_PORT}  auth: {'yes' if PROXY_AUTH else 'no'}")
    sys.stdout.flush()

    while True:
        client_sock, addr = server.accept()
        t = threading.Thread(target=handle_client, args=(client_sock, addr), daemon=True)
        t.start()


if __name__ == "__main__":
    main()
