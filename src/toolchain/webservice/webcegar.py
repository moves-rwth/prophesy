#!/usr/bin/env python3
import os
import sys
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))


import bottle
import tempfile
import argparse
import config
import sampling
from bottle import request, route, static_file, redirect
import beaker.middleware
from util import ensure_dir_exists
from input.resultfile import read_param_result, read_pstorm_result, \
    write_pstorm_result
from input.prismfile import PrismFile
from modelcheckers.param import ParamParametricModelChecker
from modelcheckers.pstorm import ProphesyParametricModelChecker


from constraints.convex_constraint import poly_constraint
import smt
from smt.smtlib import SmtlibSolver
from sympy.core.symbol import Symbol
from smt.smt import VariableDomain
from sympy.polys.polytools import Poly
from data.rationalfunction import RationalFunction
from data.constraint import Constraint

def _json_error(message, status = 500):
    """Aborts the current request with the given message"""
    from bottle import response
    import json
    # response.charset = 'UTF-8'
    response.content_type = 'application/json; charset=UTF-8'
    response.status = status
    return json.dumps({'status':'failed', 'reason':message})
    # abort(409, json.dumps({'status':'failed', 'reason':message}))

def _json_ok(data = []):
    """Returns JSON OK with formatted data"""
    from bottle import response
    import json
    # response.charset = 'UTF-8'
    response.content_type = 'application/json; charset=UTF-8'
    return json.dumps({'status':'ok', 'data':data})

def _get_session(item, default = None):
    try:
        # Attempt to access session, set-up if fails
        rqsession = request.session
    except:
        rqsession = request.session = request.environ['beaker.session']
    if not item in rqsession:
        rqsession[item] = default
    return rqsession[item]

def _set_session(item, data):
    try:
        # Attempt to access session, set-up if fails
        rqsession = request.session
    except:
        rqsession = request.session = request.environ['beaker.session']
    rqsession[item] = data
    return data

def _getResultData(name):
    result_files = _get_session('result_files', {})
    if not name in result_files:
        return None
    try:
        result = read_pstorm_result(result_files[name])
        return result
    except:
        return None

def _jsonSamples(samples):
    return [{"coordinate" : [float(x), float(y)], "value" : float(v)} for (x, y), v in samples.items()]

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

@route('/uploadPrism', method = 'POST')
def uploadPrism():
    tool = bottle.request.forms.get('mctool')
    upload_prism = bottle.request.files.get('file')
    upload_pctl = bottle.request.files.get('pctl-file')
    if tool not in ['pstorm', 'param'] or upload_prism is None or upload_pctl is None:
        return _json_error("Invalid form POST'ed")

    (_, prism_path) = tempfile.mkstemp(".prism", dir = config.WEB_RESULTFILES_DIR)
    upload_prism.save(prism_path, overwrite = True)
    prism_file = PrismFile(prism_path)

    (_, pctl_path) = tempfile.mkstemp(".pctl", dir = config.WEB_RESULTFILES_DIR)
    upload_pctl.save(pctl_path, overwrite = True)

    if tool == "param":
        prism_file.replace_parameter_keyword("param float")
        tool = ParamParametricModelChecker()
    elif tool == "pstorm":
        tool = ProphesyParametricModelChecker()
    else:
        raise RuntimeError("No supported solver available")

    result = tool.get_rational_function(prism_file, pctl_path)

    os.unlink(pctl_path)
    os.unlink(prism_path)

    (_, res_file) = tempfile.mkstemp(".result", "param", config.WEB_RESULTFILES_DIR)
    write_pstorm_result(res_file, result)

    result_files = _get_session('result_files', {})

    if upload_prism.filename in result_files:
        os.unlink(result_files[upload_prism.filename])
    result_files[upload_prism.filename] = res_file
    _set_session('current_result', upload_prism.filename)

    return _json_ok({"file" : upload_prism.filename})

@route('/uploadResult', method = 'POST')
def uploadResult():
    tool = bottle.request.forms.get('result-type')
    upload = bottle.request.files.get('file')
    if tool not in ['pstorm', 'param'] or upload is None:
        return _json_error("Invalid form POST'ed")

    result_files = _get_session('result_files', {})

    (_, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTFILES_DIR)
    upload.save(res_file, overwrite = True)

    try:
        if tool == 'pstorm':
            result = read_pstorm_result(res_file)
        elif tool == 'param':
            result = read_param_result(res_file)
        else:
            raise RuntimeError("Bad tool")
    except:
        return _json_error("Unable to parse result file")
    finally:
        os.unlink(res_file)

    # Write pstorm result as canonical
    (_, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTFILES_DIR)
    write_pstorm_result(res_file, result)

    if upload.filename in result_files:
        os.unlink(result_files[upload.filename])
    result_files[upload.filename] = res_file
    _set_session('current_result', upload.filename)

    return _json_ok({"file" : upload.filename})

@route('/listAvailableResults')
def listAvailableResults():
    return _json_ok({"results" : [k for k in _get_session('result_files', {}).keys()]})

@route('/setThreshold/<threshold:float>')
def setThreshold(threshold):
    _set_session('threshold', threshold)
    return _json_ok({'threshold': threshold})

@route('/getThreshold')
def getThreshold():
    return _json_ok({"threshold" : _get_session('threshold', 0.5)})

@route('/getResultData/<name>')
def getResultData(name):
    result_files = _get_session('result_files', {})
    if not name in result_files:
        return _json_error("Result data not found", 404)
    try:
        result = read_pstorm_result(result_files[name])
        return _json_ok({"result_data" : str(result)})
    except:
        return _json_error("Error reading result data")

@route('/getCurrentResult')
def getCurrentResult():
    name = _get_session('current_result', None)
    if name is None:
        return _json_error("No result loaded", 412)
    return _json_ok({"result" : name})

@route('/setCurrentResult/<name>')
def setCurrentResult(name):
    results = _get_session('result_files', {})
    if name in results:
        _set_session('current_result', name)
        return _json_ok({"result" : name})

    return _json_error("No result found", 404)

@route('/addSamples', method = "POST")
def addSamples():
    coordinates = bottle.request.json
    if coordinates is None:
        return _json_error("Unable to read coordinates", 400)
    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)
    samples = request.session.get('samples', {})
    for x, y in coordinates:
        point = (float(x), float(y))
        value = result.ratfunc.subs([x for x in zip(result.parameters, point)]).evalf()
        samples[point] = value
    _set_session('samples', samples)

    return _json_ok(_jsonSamples(samples))

@route('/getSamples')
def getSamples():
    flattenedsamples = _jsonSamples(_get_session('samples', {}))
    return _json_ok(flattenedsamples)

@route('/addSample/<x:float>/<y:float>')
def addSample(x, y):
    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)
    value = result.ratfunc.subs([i for i in zip(result.parameters, (x, y))]).evalf()
    samples = _get_session('samples', {})
    samples[(x, y)] = value
    return _json_ok(_jsonSamples(samples))

@route('/generateSamples/<iterations:int>/<nrsamples:int>')
def generateSamples(iterations, nrsamples):
    if iterations < 0:
        return _json_error("Number of iterations must be >= 0", 400)
    if nrsamples < 2:
        return _json_error("Number of samples must be >= 2", 400)
    threshold = _get_session('threshold', 0.5)

    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)

    intervals = [(0.01, 0.99)] * len(result.parameters)
    sampling_interface = sampling.RatFuncSampling(result.ratfunc, result.parameters)
    samples = sampling_interface.perform_uniform_sampling(intervals, nrsamples)
    for _ in range(iterations):
        samples = sampling.refine_sampling(samples, threshold, sampling_interface, True, use_filter = True)

    _set_session('samples', samples)
    return _json_ok(_jsonSamples(samples))

@route('/checkConstraints', method = 'POST')
def checkConstraints():
    coordinates = bottle.request.json
    if coordinates is None:
        return _json_error("Unable to read coordinates", 400)
    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)

    # TODO: should the constraint check for good or bad-ness?
    is_bad = False

    coordinates = [(float(x), float(y)) for x, y in coordinates]
    coordinates = coordinates[:-1]

    constraints = poly_constraint(coordinates, result.parameters)

    ###############################
    ###############################
    # This part should be put away in a function
    ###############################
    smt2interface = SmtlibSolver()
    smt2interface.run()

    threshold = _get_session('threshold', 0.5)

    for p in result.parameters:
        smt2interface.add_variable(p.name, VariableDomain.Real)
        smt2interface.assert_constraint(Constraint(Poly(p - 1.0), "<=", result.parameters))
        smt2interface.assert_constraint(Constraint(Poly(p), ">=", result.parameters))

    #TODO: allow flipped assertion?
    safe_relation = "<="
    bad_relation = ">"
    safe_objective_constraint = Constraint(Poly(result.ratfunc.nominator / result.ratfunc.denominator - threshold), safe_relation, result.parameters)
    bad_objective_constraint = Constraint(Poly(result.ratfunc.nominator / result.ratfunc.denominator - threshold), bad_relation , result.parameters)

    smt2interface.add_variable("safe", VariableDomain.Bool)
    smt2interface.add_variable("bad", VariableDomain.Bool)
    smt2interface.assert_guarded_constraint("safe", safe_objective_constraint)
    smt2interface.assert_guarded_constraint("bad", bad_objective_constraint)

    ###############################
    ###############################
    ###############################

    # check constraint with smt
    smt_model = None
    for constraint in constraints:
        smt2interface.assert_constraint(constraint)

    smt2interface.set_guard("safe", is_bad)
    smt2interface.set_guard("bad", not is_bad)
    print("Calling smt solver")
    checkresult = smt2interface.check()
    if checkresult == smt.smt.Answer.killed or checkresult == smt.smt.Answer.memout:
        return _json_error("Solver DNF", 500)
    else:
        if checkresult == smt.smt.Answer.sat:
            smt_model = smt2interface.get_model()

    smt2interface.stop()

    if checkresult == smt.smt.Answer.sat:
        # add new point as counter example to existing constraints
        # NOTE: What if value not set? Default 0,5? Error?
        pt = tuple([smt_model[p.name] for p in result.parameters])
        value = result.ratfunc.subs(smt_model.items()).evalf()
        samples = _get_session('samples', {})
        samples[pt] = value
        return _json_ok({'result':'sat', 'cex':{'coordinate':pt, 'value':float(value)}})
    elif checkresult == smt.smt.Answer.unsat:
        return _json_ok({'result':'unsat'})
    else:
        return _json_error('Solver Error')

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
        'session.invalidate_corrupt':False
    }

    app = StripPathMiddleware(beaker.middleware.SessionMiddleware(bottle.app(), session_opts))
    if(vars(cmdargs)['server_quiet']):
        print("Starting webservice...")
    bottle.run(app = app, host = vars(cmdargs)['server_host'], port = vars(cmdargs)['server_port'], debug = vars(cmdargs)['server_debug'], quiet = vars(cmdargs)['server_quiet'])
