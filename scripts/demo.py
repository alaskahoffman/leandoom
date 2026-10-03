#!/usr/bin/env python3
"""Local, read-only transport for Lean's proof companion. No game simulation."""
import argparse
import functools
import http.server
import json
import pathlib
import subprocess
import tempfile
import threading
import time
import webbrowser

ROOT = pathlib.Path(__file__).resolve().parents[1]
ROUTES = {
    '/': ('demo/index.html', 'text/html; charset=utf-8'),
    '/app.js': ('demo/app.js', 'text/javascript; charset=utf-8'),
    '/style.css': ('demo/style.css', 'text/css; charset=utf-8'),
    '/proof/movement': ('Doom/Proofs/Movement.lean', 'text/plain; charset=utf-8'),
    '/proof/aim': ('Doom/Proofs/AutoAim.lean', 'text/plain; charset=utf-8'),
    '/proof/firing': ('Doom/Proofs/Firing.lean', 'text/plain; charset=utf-8'),
}

class Handler(http.server.BaseHTTPRequestHandler):
    def __init__(self, *args, state_path, recorded=False, **kwargs):
        self.state_path = state_path
        self.recorded = recorded
        super().__init__(*args, **kwargs)

    def do_GET(self):
        path = self.path.split('?', 1)[0]
        if path == '/state':
            try:
                # Open once: atomic replacement cannot mix metadata and contents.
                with self.state_path.open() as f:
                    import os
                    age = max(0, time.time() - os.fstat(f.fileno()).st_mtime)
                    state = json.load(f)
                data = json.dumps({'state': state, 'age': age, 'recorded': self.recorded}).encode()
            except (OSError, ValueError):
                data = b'{"state":null,"age":null}'
            content_type = 'application/json'
        elif path in ROUTES:
            filename, content_type = ROUTES[path]
            data = (ROOT / filename).read_bytes()
        else:
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Content-Security-Policy', "default-src 'self'; style-src 'self' 'unsafe-inline'; connect-src 'self'; object-src 'none'; frame-ancestors 'none'")
        self.end_headers()
        try:
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def log_message(self, *_):
        pass


def server(state_path, port=0, recorded=False):
    return http.server.ThreadingHTTPServer(
        ('127.0.0.1', port), functools.partial(Handler, state_path=pathlib.Path(state_path), recorded=recorded))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-browser', action='store_true')
    parser.add_argument('--port', type=int, default=0)
    parser.add_argument('--serve', type=pathlib.Path, metavar='SNAPSHOT', help='Only serve an existing Lean snapshot (diagnostics).')
    args, viewer_args = parser.parse_known_args()
    if args.serve:
        if viewer_args:
            parser.error('viewer arguments cannot be used with --serve')
        httpd = server(args.serve, args.port, recorded=True)
        url = f'http://127.0.0.1:{httpd.server_port}/'
        print(f'Proof companion: {url}', flush=True)
        if not args.no_browser:
            webbrowser.open(url)
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            pass
        finally:
            httpd.server_close()
        return 0
    subprocess.run(['./scripts/fetch-shareware', '--offline'], cwd=ROOT, check=True)
    libdir = subprocess.check_output(['pkg-config', '--variable=libdir', 'sdl2'], text=True).strip()
    subprocess.run(['./scripts/lake', '-R', '-K', f'sdlLibDir={libdir}', 'build', 'lean-doom-viewer'], cwd=ROOT, check=True)
    # Default map also works with options such as --no-audio / --frames.
    options_with_value = {'--frames', '--telemetry'}
    positionals, skip = [], False
    for arg in viewer_args:
        if skip:
            skip = False
        elif arg in options_with_value:
            skip = True
        elif not arg.startswith('-'):
            positionals.append(arg)
    if '--telemetry' in viewer_args:
        parser.error('the demo launcher owns --telemetry; pass other viewer options normally')
    if not positionals:
        viewer_args += ['E1M1', str(ROOT/'artifacts/doom-shareware-1.9/doom1.wad')]
    with tempfile.TemporaryDirectory(prefix='lean-doom-demo-') as directory:
        snapshot = pathlib.Path(directory)/'state.json'
        httpd = server(snapshot, args.port)
        worker = threading.Thread(target=httpd.serve_forever, daemon=True)
        worker.start()
        url = f'http://127.0.0.1:{httpd.server_port}/'
        print(f'Proof companion: {url}\nPlace this browser window beside the DOOM viewer.', flush=True)
        child = None
        try:
            if not args.no_browser:
                webbrowser.open(url)
            child = subprocess.Popen([str(ROOT/'.lake/build/bin/lean-doom-viewer'), '--telemetry', str(snapshot), *viewer_args], cwd=ROOT)
            return child.wait()
        except KeyboardInterrupt:
            return 130
        finally:
            if child is not None and child.poll() is None:
                child.terminate()
                try:
                    child.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait()
            httpd.shutdown()
            httpd.server_close()
            worker.join()

if __name__ == '__main__':
    raise SystemExit(main())
