#!/usr/bin/env python3

from prophesy.config import configuration
from prophesy.util import ensure_dir_exists
from prophesy.input.resultfile import read_pstorm_result

from prophesy_web.config import configuration as web_configuration
from prophesy_web import config
from prophesy_web.application import make_app, default_results

import os
from argparse import ArgumentParser
from tornado.ioloop import IOLoop

def initEnv():
    ensure_dir_exists(web_configuration.get(config.DIRECTORIES, "web_sessions"))
    ensure_dir_exists(config.WEB_RESULTS)
    ensure_dir_exists(web_configuration.get(config.DIRECTORIES, "web_examples"))

    # Check available model checkers, solvers and various other regions
    # and adjust capabilities based on that
    global satSolvers, samplers, ppmcs
    satSolvers = configuration.getAvailableSMTSolvers()
    samplers = configuration.getAvailableSamplers()
    ppmcs = configuration.getAvailableParametricMCs()

    # Preload some result files for easy startup
    print("Loading default result files...")
    rat_path = web_configuration.get(config.DIRECTORIES, 'web_examples')
    try:
        ratfiles = os.listdir(rat_path)
        for rfile in ratfiles:
            fullpath = os.path.join(rat_path, rfile)
            try:
                read_pstorm_result(fullpath)
                default_results[rfile] = fullpath
            except:
                pass
    except:
        pass

    print("Done checking environment")

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
