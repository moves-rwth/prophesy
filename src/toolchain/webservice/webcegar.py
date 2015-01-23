#!/usr/bin/env python3
import os
import sys
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))


import bottle
import json
import tempfile
import argparse
import config
import sampling
from bottle import request, route, hook, static_file, redirect, abort
import beaker.middleware
from symbol import parameters
from util import ensure_dir_exists
from input.resultfile import read_param_result, read_pstorm_result

@hook('before_request')
def setup_request():
    request.session = request.environ['beaker.session']
    if 'threshold' not in request.session:
        request.session['threshold'] = 0.5

def _json_error(message):
    """Aborts the current request with the given message"""
    abort(409, json.dumps({'status':'failed', 'reason':message}))

def _json_ok(data = []):
    """Returns JSON OK with formatted data"""
    return json.dumps({'status':'ok', 'data':data})

def _get_session(item, default = None):
    if not item in request.session:
        request.session[item] = default
    return request.session[item]

@route('/ui/<filepath:path>')
def server_static(filepath):
    return static_file(filepath, root = config.WEB_INTERFACE_DIR)

@route('/')
def index():
    return redirect("ui/index.html", code = 301)

@route('/invalidateSession')
def invalidateSession():
    # Delete temporary files
    result_files = _get_session('result_files', {})
    for fname in result_files.values():
        try:
            os.unlink(fname)
        except:
            pass
    request.session.invalidate()
    return _json_ok()

@route('/uploadParamResult', method = 'POST')
def uploadParamResult():
    upload = bottle.request.files.get('upload')

    result_files = _get_session('result_files', {})
    results = _get_session('results', {})
    
    (_, res_file) = tempfile.mkstemp(".result", "param", config.WEB_RESULTFILES_DIR)
    with open(res_file, 'wb') as result_file:
        result_file.write(upload.file.read())

    try:
        result = read_param_result(res_file)
    except:
        os.unlink(res_file)
        _json_error("Unable to parse result file")

    if upload.filename in result_files:
        os.unlink(result_files[upload.filename])
    result_files[upload.filename] = res_file
    results[upload.filename] = result
    request.session['current_result'] = result

    return _json_ok({"file" : upload.filename})

@route('/uploadStormResult', method = 'POST')
def uploadStormResult():
    upload = bottle.request.files.get('upload')

    result_files = _get_session('result_files', {})
    results = _get_session('results', {})
    
    (_, res_file) = tempfile.mkstemp(".result", "param", config.WEB_RESULTFILES_DIR)
    with open(res_file, 'wb') as result_file:
        result_file.write(upload.file.read())

    try:
        result = read_pstorm_result(res_file)
    except:
        os.unlink(res_file)
        _json_error("Unable to parse result file")

    if upload.filename in result_files:
        os.unlink(result_files[upload.filename])
    result_files[upload.filename] = res_file
    results[upload.filename] = result
    request.session['current_result'] = result

    return _json_ok({"file" : upload.filename})

@route('/listAvailableResultFiles')
def listAvailableResults():
    return _json_ok({"result_files" : _get_session('result_files', {})})

@route('/setThreshold/<threshold:float>')
def setThreshold(threshold):
    request.session['threshold'] = threshold
    return _json_ok({'threshold': threshold})

@route('/getThreshold')
def getThreshold():
    return _json_ok({"threshold" : _get_session('threshold', {})})

@route('/getCurrentResult')
def getCurrentResult():
    return _json_ok({"result" : _get_session('current_result', None)})

@route('/manualCheckSamples', method = "POST")
def manualCheckSamples():
    spots = bottle.request.json
    if spots is None:
        return json.dumps('fail')
    print(spots)
    if 'ratfunc' not in request.session:
        return json.dumps('fail')
    if 'parameters' not in request.session:
        return json.dumps('fail')
    ratfunc = request.session['ratfunc']
    parameters = request.session['parameters']
    samples = request.session.get('samples', {})
    for spot in spots:
        value = ratfunc.evaluate(zip(parameters, [float(x) for x in spot]))
        point = tuple([float(x) for x in spot])
        samples[point] = value
    request.session['samples'] = samples

    return _json_ok()

@route('/getSamples')
def getSamples():
    flattenedsamples = [{"coordinate" : k, "value" : v} for k, v in _get_session('samples', {}).items()]
    return _json_ok(flattenedsamples)

@route('/addSample/<x:float>/<y:float>')
def addSample(x, y):
    result = _get_session('current_result', None)
    if result is None:
        _json_error("No active model loaded")
    value = result.ratfunc.subs([i for i in zip(result.parameters, (x,y))]).evalf()
    samples = _get_session('samples', {})
    samples[(x,y)] = value
    return _json_ok({"coordinate" : (x,y), "value" : value})

@route('/calculateSamples/<iterations:int>/<nrsamples:int>')
def calculateSamples(iterations, nrsamples):
    if nrsamples < 2:
        _json_error("Number of samples must be >= 2")
    result = _get_session('current_result', None)
    if result is None:
        _json_error("No active model loaded")
    threshold = _get_session('threshold', 0.5)
    samples = _get_session('samples', {})

    intervals = [(0.01, 0.99)] * len(result.parameters)
    sampling_interface = sampling.RatFuncSampling(result.ratfunc, result.parameters)
    unif_samples = sampling_interface.perform_uniform_sampling(intervals, nrsamples)
    for us, usv in unif_samples.items():
        samples[us] = usv
    samples = sampling.refine_sampling(unif_samples, threshold, sampling_interface , True)
    for _ in range(iterations):
        samples = sampling.refine_sampling(samples, threshold, sampling_interface, True, use_filter = True)

    request.session['samples'] = samples
    flattenedsamples = [{"coordinate" : k, "value" : v} for k, v in _get_session('samples', {}).items()]
    return _json_ok(flattenedsamples)

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

# strips trailing slashes from requests
class StripPathMiddleware(object):
    def __init__(self, app):
        self.app = app
    def __call__(self, e, h):
        e['PATH_INFO'] = e['PATH_INFO'].rstrip('/')
        return self.app(e, h)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Start a webservice for ' + config.TOOLNAME)
    parser.add_argument('--server-port', type = int, help = 'the port the server listens on', default = 4242)
    parser.add_argument('--server-host', help = "server host name", default = "localhost")
    parser.add_argument('--server-debug', type = bool, help = 'run the server in debug mode', default = True)
    parser.add_argument('--server-quiet', type = bool, help = 'run the server in quiet mode', default = False)
    cmdargs = parser.parse_args()

    ensure_dir_exists(config.WEB_SESSIONS_DIR)
    ensure_dir_exists(config.WEB_RESULTFILES_DIR)

    session_opts = {
        'session.type': 'file',
        'session.data_dir': config.WEB_SESSIONS_DIR,
        'session.auto': True,
    }

    app = StripPathMiddleware(beaker.middleware.SessionMiddleware(bottle.app(), session_opts))
    if(vars(cmdargs)['server_quiet']):
        print("Starting webservice...")
    bottle.run(app = app, host = vars(cmdargs)['server_host'], port = vars(cmdargs)['server_port'], debug = vars(cmdargs)['server_debug'], quiet = vars(cmdargs)['server_quiet'])
