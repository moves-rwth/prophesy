#!/usr/bin/env python3

from prophesy_web import config
from prophesy_web.application import initEnv, make_app

from argparse import ArgumentParser
from tornado.ioloop import IOLoop

def parse_cli_args():
    parser = ArgumentParser(description='Start a webservice for ' + config.TOOLNAME)
    parser.add_argument('--server-port', type=int, help='the port the server listens on', default=4242)
    parser.add_argument('--server-host', help="server host name", default="localhost")
    parser.add_argument('--server-debug', type=bool, help='run the server in debug mode', default=True)
    parser.add_argument('--server-quiet', type=bool, help='run the server in quiet mode', default=False)
    return parser.parse_args()


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    initEnv()

    app = make_app(cmdargs.server_host)

    if(not cmdargs.server_quiet):
        print("Starting webservice...")

    app.listen(cmdargs.server_port)
    IOLoop.current().start()
