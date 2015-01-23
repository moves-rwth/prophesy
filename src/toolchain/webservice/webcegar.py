#!/usr/bin/env python3
import sys
import os
from input.comics import get_polynomials_from_comics_file
from output.smt2 import smt2_to_file, call_smt_solver
from symbol import parameters
from buildconstraints import samples
from util import ensure_dir_exists
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

from config import WEB_INTERMEDIATE_FILES_DIR, WEB_INTERFACE_DIR, TOOLNAME, \
    WEBSESSIONS_DIR

import bottle
from bottle import request, route, hook, static_file, redirect, abort
import beaker.middleware
import json

import argparse
from data.rationalfunction import RationalFunction
import sampling

RESULTFILES_DIR = os.path.join(WEB_INTERMEDIATE_FILES_DIR, "results/")

@hook('before_request')
def setup_request():
    request.session = request.environ['beaker.session']
    if 'threshold' not in request.session:
        request.session['threshold'] = 0.5

@route('/ui/<filepath:path>')
def server_static(filepath):
    return static_file(filepath, root = WEB_INTERFACE_DIR)

@route('/')
def index():
    return redirect("ui/index.html", code = 301)

@route('/invalidateSession')
def invalidateSession():
    request.session.invalidate()

@route('/uploadComicsResult', method = 'POST')
def uploadComicsResult():
    upload = bottle.request.files.get('upload')
#    name, ext = os.path.splitext(upload.filename)
#    if ext not in ('.png','.jpg','.jpeg'):
#        return 'File extension not allowed.'

#    save_path = get_save_path_for_category(category)
    save_path = os.path.join(RESULTFILES_DIR, upload.filename)
    inputfile = open(save_path, 'wb')
    inputfile.write(upload.file.read())
    inputfile.close()
    return 'OK'


@route('/listAvailableResultFiles')
def loadAvailableResults():
    files = [f for f in os.listdir(RESULTFILES_DIR) if f.endswith('.pol')]
    files.sort()
    return json.dumps(files)

@route('/loadComicsResult/<filename>')
def loadComicsResult(filename):
    filepath = os.path.join(RESULTFILES_DIR, filename)
    [parameters, constraints, nominator, denominator] = get_polynomials_from_comics_file(filepath)

    request.session['name'] = filename
    request.session['constraints'] = constraints
    request.session['parameters'] = parameters
    request.session['ratfunc'] = RationalFunction(nominator, denominator)
    request.session['samples'] = {}
    print(str(request.session['ratfunc']))
    return json.dumps([str(request.session['ratfunc'])])

@route('/setThreshold/<threshold:float>')
def setThreshold(threshold):
    request.session['threshold'] = threshold

@route('/showRationalFunction')
def showRationalFunction():
    if 'ratfunc' in request.session:
        return json.dumps([str(request.session['ratfunc'])])

@route('/manualCheckSamples', method = "POST")
def manualCheckSamples():
    spots = bottle.request.json
    print(spots)
    if 'ratfunc' not in request.session:
        return 'fail'
    if 'parameters' not in request.session:
        return 'fail'
    ratfunc = request.session['ratfunc']
    parameters = request.session['parameters']
    samples = request.session.get('samples', {})
    for spot in spots:
        value = ratfunc.evaluate(zip(parameters, [float(x) for x in spot]))
        point = tuple([float(x) for x in spot])
        samples[point] = value
    request.session['samples'] = samples

    return json.dumps('ok')



@route('/calculateSamples/<iterations:int>/<nrsamples:int>')
def calculateSamples(iterations, nrsamples):

    if 'ratfunc' not in request.session:
        abort(409, 'rational function required')
    if 'parameters' not in request.session:
        abort(409, 'parameters required')
    ratfunc = request.session['ratfunc']
    print(ratfunc)
    parameters = request.session['parameters']
    print(parameters)
    threshold = request.session['threshold']
    sampling_interface = sampling.RatFuncSampling(ratfunc, parameters)
    intervals = [(0.01, 0.99)] * len(parameters)
    samples = request.session['samples']
    unif_samples = sampling_interface.perform_uniform_sampling(intervals, 4)
    for us, usv in unif_samples.items():
        samples[us] = usv
    print('refine')
    samples = sampling.refine_sampling(samples, threshold, sampling_interface , True)
    print('refine')
    samples = sampling.refine_sampling(samples, threshold, sampling_interface, True, use_filter = True)
    samples = sampling.refine_sampling(samples, threshold, sampling_interface, True, use_filter = True)
    print('done')
    request.session['samples'] = samples
    flattenedsamples = list([{"coordinates" : [str(c) for c in k], "value" : str(v)} for k, v in samples.items()])
    print(flattenedsamples)
    return json.dumps(flattenedsamples)

@route('/checkConstraints', method = 'POST')
def checkConstraints():
    check = bottle.request.json
    print(check)

    # export problem as smt2
    smt2_to_file(request.session['name'],
                 request.session['parameters'],
                 request.session['constraints'] + extra_constraints,
                 request.session['ratfunc'],
                 request.session['ratfunc'],
                 request.session['threshold'],
                 request.session['excluded_regions'],
                 safity)
    # call smt solver
    (smtres, model) = call_smt_solver("z3", request.session['name'])

    if smtres == "sat":
        modelPoint = tuple([model[p.name] for p in parameters])
        print(modelPoint)
        samples[modelPoint] = ratfunc.evaluate(list(model.items()))
        print(samples)
    else:
        samples = remove_covered_samples(parameters, samples, extra_constraints)
        if safity:
            safe.append(extra_constraints)
        else:
            bad.append(extra_constraints)
        excluded_regions.append(extra_constraints)
        print(safe)
        print(bad)

@route('/getSamples')
def getSamples():
    if 'samples' in request.session:
        flattenedsamples = list([{"coordinates" : [str(c) for c in k], "value" : str(v)} for k, v in request.session['samples'].items()])
        return json.dumps(flattenedsamples)
    else:
        return json.dumps([])

# strips trailing slashes from requests
class StripPathMiddleware(object):
    def __init__(self, app):
        self.app = app
    def __call__(self, e, h):
        e['PATH_INFO'] = e['PATH_INFO'].rstrip('/')
        return self.app(e, h)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Start a webservice for ' + TOOLNAME)
    parser.add_argument('--server-port', type = int, help = 'the port the server listens on', default = 4242)
    parser.add_argument('--server-host', help = "server host name", default = "localhost")
    parser.add_argument('--server-debug', type = bool, help = 'run the server in debug mode', default = True)
    parser.add_argument('--server-quiet', type = bool, help = 'run the server in quiet mode', default = False)
    cmdargs = parser.parse_args()

    ensure_dir_exists(WEB_INTERMEDIATE_FILES_DIR)
    ensure_dir_exists(RESULTFILES_DIR)

    session_opts = {
        'session.type': 'file',
        'session.data_dir': WEBSESSIONS_DIR,
        'session.auto': True,
    }

    app = StripPathMiddleware(beaker.middleware.SessionMiddleware(bottle.app(), session_opts))
    if(vars(cmdargs)['server_quiet']):
        print("Starting webservice...")
    bottle.run(app = app, host = vars(cmdargs)['server_host'], port = vars(cmdargs)['server_port'], debug = vars(cmdargs)['server_debug'], quiet = vars(cmdargs)['server_quiet'])
