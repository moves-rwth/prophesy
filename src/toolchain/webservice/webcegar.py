#!/usr/bin/env python3
import os
import sys
import shutil
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))
sys.path.insert(0, os.path.join(thisfilepath, '../../lib'))

import json
import bottle
import tempfile
import argparse
import config
from bottle import request, route, static_file, redirect, error
import beaker.middleware
from util import ensure_dir_exists, run_tool
from input.resultfile import read_param_result, read_pstorm_result, \
    write_pstorm_result
from input.prismfile import PrismFile
from modelcheckers.param import ParamParametricModelChecker
from modelcheckers.pstorm import ProphesyParametricModelChecker
from smt.smt import setup_smt
from smt.isat import IsatSolver
from smt.smtlib import SmtlibSolver
from sampling.sampler_ratfunc import RatFuncSampling
from sampling.sampler_prism import McSampling
from sampling.sampling_uniform import UniformSampleGenerator
from sampling.sampling_linear import LinearRefinement
from sampling.sampling_delaunay import DelaunayRefinement
from constraints.constraint_planes import ConstraintPlanes
from constraints.constraint_rectangles import ConstraintRectangles
from constraints.constraint_quads import ConstraintQuads
from constraints.constraint_polygon import ConstraintPolygon
from shapely.geometry.polygon import Polygon

pmcCheckers = {}
samplers = {}
satSolvers = {}

default_results = {}

def _json_error(message, status = 500):
    """Aborts the current request with the given message"""
    from bottle import response
    # response.charset = 'UTF-8'
    response.content_type = 'application/json; charset=UTF-8'
    response.status = status
    print("({}) {}".format(status, message))
    return json.dumps({'status':'failed', 'reason':message})
    # abort(409, json.dumps({'status':'failed', 'reason':message}))

def _json_ok(data = []):
    """Returns JSON OK with formatted data"""
    from bottle import response
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

def _jsonPoly(polygon):
    if isinstance(polygon, Polygon):
        return _jsonPoly(polygon.exterior)
    return [[pt[0], pt[1]] for pt in polygon.coords]

def getSat(satname):
    if satname == 'z3':
        return SmtlibSolver()
    elif satname == 'isat':
        return IsatSolver()
    else:
        raise RuntimeError("Unknown SAT solver requested")

def getSampler(satname, result):
    if satname == 'ratfunc':
        # Do not use rationals for now
        return RatFuncSampling(result.ratfunc, result.parameters, False)
    elif satname == 'prism':
        return McSampling(result.prism_file, result.pctl_file)
    else:
        raise RuntimeError("Unknown sampler requested")

def getPMC(satname):
    if satname == 'pstorm':
        return ProphesyParametricModelChecker()
    elif satname == 'param':
        return ParamParametricModelChecker();
    else:
        raise RuntimeError("Unknown PMC requested")

@error(500)
def handle_error(http_error):
    # (code, message, exc, tb) = http_error.status, http_error.body, http_error.exception, http_error.traceback
    # return bottle.HTTPResponse(status=200, body=)
    return _json_error("{}: {}".format(http_error.body, http_error.exception))

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

@route('/setThreshold/<threshold:float>')
def setThreshold(threshold):
    _set_session('threshold', threshold)
    return getThreshold()

@route('/getThreshold')
def getThreshold():
    return _json_ok(_get_session('threshold', 0.5))

@route('/listEnvironment')
def listEnv():
    return _json_ok({"pmc":pmcCheckers, "samplers":samplers, "sat":satSolvers})

@route('/getEnvironment')
def getEnv():
    return _json_ok({
                     "pmc" :     _get_session("pmc", next(iter(pmcCheckers.keys()))),
                     "sampler" : _get_session("sampler", 'ratfunc'),
                     "sat" :     _get_session("sat", next(iter(satSolvers.keys())))})

@route('/setEnvironment', method = 'POST')
def setEnv():
    pmc = bottle.request.forms.get('pmc')
    sampler = bottle.request.forms.get('sampler')
    sat = bottle.request.forms.get('sat')
    if not pmc in pmcCheckers:
        return _json_error("Invalid model checker")
    if not sampler in samplers:
        return _json_error("Invalid sampler")
    if not sat in satSolvers:
        return _json_error("Invalid SAT solver")
    # TODO: pmc is not really a global setting,
    # depends on upload form
    _set_session("pmc", pmc)
    _set_session("sampler", sampler)
    _set_session("sat", sat)

    return getEnv()

@route('/uploadPrism', method = 'POST')
def uploadPrism():
    tool = bottle.request.forms.get('mctool')
    upload_prism = bottle.request.files.get('file')
    upload_pctl = bottle.request.files.get('pctl-file')
    if tool not in pmcCheckers.keys():
        return _json_error("Invalid tool selected")
    if upload_prism is None:
        return _json_error("Missing PRISM file")
    if upload_pctl is None:
        return _json_error("Missing PCTL file")

    (_, prism_path) = tempfile.mkstemp(".prism", dir = config.WEB_RESULTFILES_DIR)
    upload_prism.save(prism_path, overwrite = True)
    prism_file = PrismFile(prism_path)

    (_, pctl_path) = tempfile.mkstemp(".pctl", dir = config.WEB_RESULTFILES_DIR)
    upload_pctl.save(pctl_path, overwrite = True)

    if tool == "param":
        prism_file.replace_parameter_keyword("param float")
    tool = getPMC(tool)

    try:
        result = tool.get_rational_function(prism_file, pctl_path)
    except Exception as e:
        return _json_error("Error while computing rational function: {}".format(e))

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
    # Note: this is not the list of pmcCheckers, but of available result parsers
    if tool not in ['pstorm', 'param']:
        return _json_error("Invalid tool selected")
    if upload is None:
        return _json_error("Missing result file")

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
    results = _get_session('result_files', {})
    if len(results) == 0 and len(default_results) > 0:
        # Copy over default results
        for name, path in default_results.items():
            (_, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTFILES_DIR)
            results[name] = res_file
            shutil.copyfile(path, res_file)
        _set_session('result_files', results)
        _set_session('current_result', next(iter(results)))
    return _json_ok({"results" : {k:k for k in results.keys()}})

@route('/getResultData/<name>')
def getResultData(name):
    result_files = _get_session('result_files', {})
    if not name in result_files:
        return _json_error("Result data not found", 404)
    try:
        result = read_pstorm_result(result_files[name])
        return _json_ok(str(result))
    except:
        return _json_error("Error reading result data")

@route('/getCurrentResult')
def getCurrentResult():
    name = _get_session('current_result', None)
    if name is None:
        if len(default_results) > 0:
            name = next(iter(default_results))
            _set_session('current_result', name)
    if name is None:
        return _json_error("No result loaded", 412)
    return _json_ok(name)

@route('/setCurrentResult/<name>')
def setCurrentResult(name):
    results = _get_session('result_files', {})
    if name in results:
        _set_session('current_result', name)
        return _json_ok(name)

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
        value = result.ratfunc.eval({x : v for x, v in zip(result.parameters, point)})
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

    sampler = getSampler(_get_session('sampler'), result)
    new_samples = sampler.perform_sampling([(x, y)])
    samples = _get_session('samples', {})
    samples.update(new_samples)
    return _json_ok(_jsonSamples(samples))

@route('/generateSamples', method = 'POST')
def generateSamples():
    nrsamples = int(bottle.request.forms.get('sampling'))
    iterations = int(bottle.request.forms.get('iterations'))

    if iterations < 0:
        return _json_error("Number of iterations must be >= 0", 400)
    if nrsamples < 2:
        return _json_error("Number of samples must be >= 2", 400)
    threshold = _get_session('threshold', 0.5)
    generator_type = bottle.request.forms.get('generator')
    if not generator_type in ['linear', 'delaunay']:
        return _json_error("Invalid generator set " + generator_type, 400)

    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)

    samples = {}
    intervals = [(0.01, 0.99)] * len(result.parameters)
    sampling_interface = getSampler(_get_session('sampler'), result)
    uniform_generator = UniformSampleGenerator(sampling_interface, intervals, nrsamples)
    for new_samples in uniform_generator:
        samples.update(new_samples)

    if generator_type == "linear":
        refinement_generator = LinearRefinement(sampling_interface, samples, threshold)
    elif generator_type == "delaunay":
        refinement_generator = DelaunayRefinement(sampling_interface, samples, threshold)
    else:
        assert False, "Bad generator"
    # Using range to limit the number of iterations
    for (new_samples, _) in zip(refinement_generator, range(0, iterations)):
        samples.update(new_samples)

    _set_session('samples', samples)
    return _json_ok(_jsonSamples(samples))

@route('/clearSamples')
def clearSamples():
    _set_session("samples", {})
    return _json_ok()

@route('/checkConstraint', method = 'POST')
def checkConstraint():
    mode = bottle.request.forms.get('constr-mode')
    if not mode in ['safe', 'bad']:
        return _json_error("Invalid mode set", 400)

    coordinates = bottle.request.forms.get('coordinates')
    if coordinates is None:
        return _json_error("Unable to read coordinates", 400)
    coordinates = json.loads(bottle.request.forms.get('coordinates'))
    if coordinates is None or len(coordinates) < 3:
        return _json_error("Unable to parse coordinates", 400)

    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)

    samples = _get_session('samples', {})

    threshold = _get_session('threshold', 0.5)

    coordinates = [(float(x), float(y)) for x, y in coordinates]
    if coordinates[0] == coordinates[-1]:
        # Strip connecting point if any
        coordinates = coordinates[:-1]

    smt2interface = getSat(_get_session('sat'))
    smt2interface.run()
    setup_smt(smt2interface, result, threshold)

    polygon = Polygon(coordinates)
    generator = ConstraintPolygon(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
    generator.plot = False
    generator.add_polygon(polygon, mode == "safe")

    (safe_poly, bad_poly, new_samples) = generator.generate_constraints(10)
    samples.update(new_samples)

    smt2interface.stop()

    unsat = []
    for poly in safe_poly:
        unsat.append((_jsonPoly(poly), True))
    for poly in bad_poly:
        unsat.append((_jsonPoly(poly), False))

    if len(new_samples) == 0 and len(unsat) == 0:
        return _json_error("SAT solver did not return an answer")

    return _json_ok({'sat':_jsonSamples(new_samples), 'unsat':unsat})

@route('/generateConstraints', method = 'POST')
def generateConstraints():
    generator_type = bottle.request.forms.get('generator')
    if not generator_type in ['planes', 'rectangles', 'quads']:
        return _json_error("Invalid generator set", 400)

    result = _getResultData(_get_session('current_result', None))
    if result is None:
        return _json_error("Unable to load result data", 500)

    samples = _get_session('samples', {})
    threshold = _get_session('threshold', 0.5)

    smt2interface = getSat(_get_session('sat'))
    smt2interface.run()
    setup_smt(smt2interface, result, threshold)

    if generator_type == 'planes':
        generator = ConstraintPlanes(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
    elif generator_type == 'rectangles':
        generator = ConstraintRectangles(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
    elif generator_type == 'quads':
        generator = ConstraintQuads(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
    else:
        return _json_error("Bad generator")
    generator.plot = False

    unsat = []
    new_samples = {}
    for check_result, _ in zip(generator, range(0,25)):
        (is_unsat, data) = check_result
        if is_unsat:
            (constraint, poly, safe) = data
            unsat.append((_jsonPoly(poly), safe))
        else:
            (point, value) = data
            new_samples[point] = value
            samples[point] = value

    smt2interface.stop()

    if len(new_samples) == 0 and len(unsat) == 0:
        return _json_error("SAT solver did not return an answer")

    return _json_ok({'sat':_jsonSamples(new_samples), 'unsat':unsat})

def initEnv():
    # Check available model checkers, solvers and various other constraints
    # and adjust capabilities based on that
    print("Checking available tools...")

    try:
        run_tool([config.PARAM_COMMAND], True)
        pmcCheckers['param'] = "Param"
        print("Found param")
    except:
        pass
    try:
        print(config.PARAMETRIC_STORM_COMMAND)
        run_tool([config.PARAMETRIC_STORM_COMMAND], True)
        pmcCheckers['pstorm'] = "Parametric Storm"
        print("Found pstorm")
    except:
        pass

    samplers['ratfunc'] = "Rational function"
    try:
        # TODO: Prism sampling not yet supported
        #run_tool([config.PRISM_COMMAND], True)
        #samplers['prism'] = "PRISM"
        #print("Found prism")
        pass
    except:
        pass

    try:
        run_tool([config.Z3_COMMAND], True)
        satSolvers['z3'] = "Z3"
        print("Found z3")
    except:
        pass
    try:
        run_tool([config.SMTRAT_COMMAND], True)
        satSolvers['isat'] = "iSAT"
        print("Found isat")
    except:
        pass

    if len(pmcCheckers) == 0:
        raise RuntimeError("No model checkers in environment")
    if len(samplers) == 0:
        # The astute programmer can see that this should never happen
        raise RuntimeError("No samplers in environment")
    if len(satSolvers) == 0:
        raise RuntimeError("No SAT solvers in environment")

    # Preload some result files for easy startup
    print("Loading default result files...")
    rat_path = os.path.join(config.EXAMPLES_DIR, 'rat_files')
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

    initEnv()

    app = StripPathMiddleware(beaker.middleware.SessionMiddleware(bottle.app(), session_opts))
    if(vars(cmdargs)['server_quiet']):
        print("Starting webservice...")
    bottle.run(app = app, host = vars(cmdargs)['server_host'], port = vars(cmdargs)['server_port'], debug = vars(cmdargs)['server_debug'], quiet = vars(cmdargs)['server_quiet'])
