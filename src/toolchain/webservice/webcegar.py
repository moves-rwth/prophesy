#!/usr/bin/env python3
import os
import sys
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))
sys.path.insert(0, os.path.join(thisfilepath, '../../lib'))

import tempfile
import re
import argparse
import shutil
import uuid

from tornado.ioloop import IOLoop
from tornado.web import Application, RequestHandler
from tornado.websocket import WebSocketHandler
from tornado.escape import json_decode
from pycket.session import SessionMixin

import config
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

#@route('/ui/<filepath:path>')
def server_static(filepath):
    return static_file(filepath, root = config.WEB_INTERFACE_DIR)

#@route('/')
def index():
    return redirect("ui/index.html", code = 301)

class CegarHandler(RequestHandler, SessionMixin):
    def write_error(self, status_code, **kwargs):
        message = "Unknown server error"
        if "exc_info" in kwargs:
            (type, value, traceback) = kwargs["exc_info"]
            message = str(value)
        self._json_error(message = message, status = status_code)

    def _json_error(self, message, status = 500):
        """Aborts the current request with the given message"""
        print("({}) {}".format(status, message))
        self.set_status(status)
        self.write({'status':'failed', 'reason':message})

    def _json_ok(self, data = []):
        """Returns JSON OK with formatted data"""
        self.write({'status':'ok', 'data':data})

    def _get_session(self, item, default = None):
        if not item in self.session:
            self.session.set(item, default)
        return self.session.get(item, default)

    def _set_session(self, item, data):
        self.session.set(item, data)
        return data


    def _getResultData(self, name):
        result_files = self._get_session('result_files', {})
        if not name in result_files:
            return None
        try:
            result = read_pstorm_result(result_files[name])
            return result
        except:
            return None

    def setup_results(self):
        results = self._get_session('result_files', None)
        if results is None:
            # Copy over default results
            results = {}
            for name, path in default_results.items():
                (res_fd, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTFILES_DIR)
                os.close(res_fd)
                results[name] = res_file
                shutil.copyfile(path, res_file)
            self._set_session('result_files', results)
            self._set_session('current_result', next(iter(results.keys())))

    def _get_socket(self):
        socket_id = self._get_session('socket_id', None)
        if not socket_id in CegarWebSocket.socket_list:
            return None
        return CegarWebSocket.socket_list[socket_id]

    def open(self):
        self.id = uuid.uuid4()
        self.session.set('socket_id', self.id)

#@route('/invalidateSession')
class InvalidateSession(CegarHandler):
    def get(self):
        # Delete temporary files
        result_files = self._get_session('result_files', {})
        for fname in result_files.values():
            try:
                os.unlink(fname)
            except:
                pass
        request.session.invalidate()
        return self._json_ok()

#@route('/threshold')
class Threshold(CegarHandler):
    def get(self):
        return self._json_ok(self._get_session('threshold', 0.5))

    def post(self):
        return self.put()

    def put(self):
        # threshold = self.get_argument('threshold', None)
        threshold = json_decode(self.request.body)
        threshold = float(threshold)
        self._set_session('threshold', threshold)

        # Clear all constraints, they are no longer valid
        self._set_session('constraints', [])

#@route('/currentResult')
class CurrentResult(CegarHandler):
    def get(self):
        self.setup_results()
        name = self._get_session('current_result', None)
        if name is None:
            return self._json_error("No result loaded", 412)
        return self._json_ok(name)

    def post(self):
        name = self.get_argument('name')
        results = self._get_session('result_files', {})
        if name in results:
            self._set_session('current_result', name)
            return self._json_ok(name)

        return self._json_error("No result found", 404)

#@route('/environment')
class Environment(CegarHandler):
    def get(self):
        return self._json_ok({
                         "pmc" :     self._get_session("pmc", next(iter(pmcCheckers.keys()))),
                         "sampler" : self._get_session("sampler", 'ratfunc'),
                         "sat" :     self._get_session("sat", next(iter(satSolvers.keys())))})

    def post(self):
        pmc = self.get_argument('pmc')
        sampler = self.get_argument('sampler')
        sat = self.get_argument('sat')
        if not pmc in pmcCheckers:
            return self._json_error("Invalid model checker")
        if not sampler in samplers:
            return self._json_error("Invalid sampler")
        if not sat in satSolvers:
            return self._json_error("Invalid SAT solver")
        # TODO: pmc is not really a global setting,
        # depends on upload form
        self._set_session("pmc", pmc)
        self._set_session("sampler", sampler)
        self._set_session("sat", sat)

        return get()

#@route('/environments')
class Environments(CegarHandler):
    def get(self):
        return self._json_ok({"pmc":pmcCheckers, "samplers":samplers, "sat":satSolvers})

#@route('/results')
class Results(CegarHandler):
    def get(self, name=None):
        self.setup_results()
        results = self._get_session('result_files', {})
        if name is None:
            return self._json_ok({k:k for k in results.keys()})
        else:
            if not name in result_files:
                return self._json_error("Result data not found", 404)
            try:
                result = read_pstorm_result(result_files[name])
            except:
                return self._json_error("Error reading result data")
            str_result = str(result)
            # Replace ** with superscript
            str_result = re.sub(r'\*\*(\d+)', r'<sub>\1</sub>', str_result)
            # Replace * with dot symbol
            str_result = re.sub(r'\*', r'&#183;', str_result)
            # Replace <= with symbol
            str_result = re.sub(r'\<\=', r'&#8804;', str_result)
            # Replace >= with symbol
            str_result = re.sub(r'\>\=', r'&#8805;', str_result)
            return self._json_ok(str_result)

#@route('/uploadPrism', method = 'POST')
class UploadPrism(CegarHandler):
    def post(self):
        tool = self.get_argument('mctool')
        upload_prism = self.request.files['file'][0]
        upload_pctl = self.request.files['pctl-file'][0]
        if tool not in pmcCheckers.keys():
            return self._json_error("Invalid tool selected")
        if upload_prism is None:
            return self._json_error("Missing PRISM file")
        if upload_pctl is None:
            return self._json_error("Missing PCTL file")

        (prism_fd, prism_path) = tempfile.mkstemp(".prism", dir = config.WEB_RESULTFILES_DIR)
        with os.fdopen(prism_fd) as prism_f:
            prism_f.write(upload_prism.body)
        prism_file = PrismFile(prism_path)

        (pctl_fd, pctl_path) = tempfile.mkstemp(".pctl", dir = config.WEB_RESULTFILES_DIR)
        with os.fdopen(pctl_fd) as pctl_f:
            pctl_f.write(upload_pctl.body)

        if tool == "param":
            prism_file.replace_parameter_keyword("param float")
        tool = getPMC(tool)

        try:
            result = tool.get_rational_function(prism_file, pctl_path)
        except Exception as e:
            return self._json_error("Error while computing rational function: {}".format(e))

        os.unlink(pctl_path)
        os.unlink(prism_path)

        (res_fd, res_file) = tempfile.mkstemp(".result", "param", config.WEB_RESULTFILES_DIR)
        os.close(res_fd)
        write_pstorm_result(res_file, result)

        result_files = self._get_session('result_files', {})

        if upload_prism.filename in result_files:
            os.unlink(result_files[upload_prism.filename])
        result_files[upload_prism.filename] = res_file
        self._set_session('current_result', upload_prism.filename)

        return self._json_ok(upload_prism.filename)

#@route('/uploadResult', method = 'POST')
class UploadResult(CegarHandler):
    def post(self):
        tool = self.get_argument('result-type')
        upload = self.request.files['file'][0]
        # Note: this is not the list of pmcCheckers, but of available result parsers
        if tool not in ['pstorm', 'param']:
            return self._json_error("Invalid tool selected")
        if upload is None:
            return self._json_error("Missing result file")

        result_files = self._get_session('result_files', {})

        (res_fd, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTFILES_DIR)
        with os.fdopen(res_fd) as res_f:
            res_f.write(upload.body)

        try:
            if tool == 'pstorm':
                result = read_pstorm_result(res_file)
            elif tool == 'param':
                result = read_param_result(res_file)
            else:
                raise RuntimeError("Bad tool")
        except:
            return self._json_error("Unable to parse result file")
        finally:
            os.unlink(res_file)

        # Write pstorm result as canonical
        (res_fd, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTFILES_DIR)
        os.close(res_fd)
        write_pstorm_result(res_file, result)

        if upload.filename in result_files:
            os.unlink(result_files[upload.filename])
        result_files[upload.filename] = res_file
        self._set_session('current_result', upload.filename)

        return self._json_ok({"file" : upload.filename})


#@route('/samples', method = "POST")
class Samples(CegarHandler):
    def get(self):
        flattenedsamples = _jsonSamples(self._get_session('samples', {}))
        return self._json_ok(flattenedsamples)

    def post(self):
        coordinates = json_decode(self.request.body)
        if coordinates is None:
            return self._json_error("Unable to read coordinates", 400)
        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)
        samples = request.session.get('samples', {})
        for x, y in coordinates:
            point = (float(x), float(y))
            value = result.ratfunc.eval({x : v for x, v in zip(result.parameters, point)})
            samples[point] = value
        self._set_session('samples', samples)

        return self._json_ok(self._jsonSamples(samples))

    def put(self):
        coordinate = json_decode(self.request.body)
        try:
            x = coordinate[0]
            y = coordinate[1]
        except:
            return self._json_error('Unable to parse coordinate', 400)

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        sampler = getSampler(self._get_session('sampler'), result)
        new_samples = sampler.perform_sampling([(x, y)])
        samples = self._get_session('samples', {})
        samples.update(new_samples)
        # return _json_ok(_jsonSamples(samples))
        # TODO: redirect?

    def delete(self):
        self._set_session("samples", {})
        return self._json_ok()

#@route('/generateSamples', method = 'POST')
class GenerateSamples(CegarHandler):
    def get(self):
        nrsamples = int(self.get_argument('sampling'))
        iterations = int(self.get_argument('iterations'))

        if iterations < 0:
            return self._json_error("Number of iterations must be >= 0", 400)
        if nrsamples < 2:
            return self._json_error("Number of samples must be >= 2", 400)
        threshold = self._get_session('threshold', 0.5)
        generator_type = self.get_argument('generator')
        if not generator_type in ['linear', 'delaunay']:
            return self._json_error("Invalid generator set " + generator_type, 400)

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        socket = self._get_socket()

        samples = {}
        intervals = [(0.01, 0.99)] * len(result.parameters)
        sampling_interface = getSampler(_get_session('sampler'), result)
        uniform_generator = UniformSampleGenerator(sampling_interface, intervals, nrsamples)
        for new_samples in uniform_generator:
            samples.update(new_samples)
            if socket is not None:
                socket.send_samples(new_samples)

        if generator_type == "linear":
            refinement_generator = LinearRefinement(sampling_interface, samples, threshold)
        elif generator_type == "delaunay":
            refinement_generator = DelaunayRefinement(sampling_interface, samples, threshold)
        else:
            assert False, "Bad generator"
        # Using range to limit the number of iterations
        for (new_samples, _) in zip(refinement_generator, range(0, iterations)):
            samples.update(new_samples)
            if socket is not None:
                socket.send_samples(new_samples)

        self._set_session('samples', samples)
        return self._json_ok(_jsonSamples(samples))

class ConstraintHandler(CegarHandler):
    def make_gen(self, type):
        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        samples = self._get_session('samples', {})
        threshold = self._get_session('threshold', 0.5)

        smt2interface = getSat(self._get_session('sat'))
        smt2interface.run()
        setup_smt(smt2interface, result, threshold)

        if type == 'planes':
            generator = ConstraintPlanes(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
        elif type == 'rectangles':
            generator = ConstraintRectangles(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
        elif type == 'quads':
            generator = ConstraintQuads(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
        elif type == 'poly':
            generator = ConstraintPolygon(samples, result.parameters, threshold, 0.01, smt2interface, result.ratfunc)
        else:
            return self._json_error("Bad generator")
        generator.plot = False

        return (smt2interface, generator)

    def analyze(self, smt2interface, generator, iterations = -1):
        if iterations == 0:
            return ({}, [])

        socket = self._get_socket()

        smtinterface.run()

        unsat = []
        new_samples = {}
        for check_result in generator:
            (is_unsat, data) = check_result
            if is_unsat:
                (constraint, poly, safe) = data
                unsat.append((_jsonPoly(poly), bool(safe)))
                if socket is not None:
                    socket.send_constraints([unsat[-1]])
            else:
                (point, value) = data
                new_samples[point] = value
                samples[point] = value
                if socket is not None:
                    socket.send_samples({point:value})

            iterations -= 1
            if iterations == 0:
                break

        smtinterface.stop()
        
        return (new_samples, unsat)

#@route('/constraints')
class Constraints(ConstraintHandler):
    def get(self):
        constraints = self._get_session('constraints', [])
        return self._json_ok(constraints)

    def post(self):
        request = json_decode(self.request.body)
        safe = bool(request['safe'])

        coordinates = request['coordinates']
        if coordinates is None:
            return self._json_error("Unable to read coordinates", 400)
        coordinates = [(float(x), float(y)) for x, y in coordinates]
        if coordinates[0] == coordinates[-1]:
            # Strip connecting point if any
            coordinates = coordinates[:-1]

        smt2interface, generator = self.make_gen("poly")
        generator.add_polygon(coordinates, safe)
        new_samples, unsat = self.analyze(smt2interface, generator)

        if len(new_samples) == 0 and len(unsat) == 0:
            return self._json_error("SMT solver did not return an answer")

        samples = self._get_session('samples', {})
        constraints = self._get_session('constraints', [])

        samples.update(new_samples)
        constraints.append(unsat)

        return self._json_ok({'sat':_jsonSamples(new_samples), 'unsat':unsat})
        # TODO: redirect?

    def delete(self):
        self._set_session('constraints', {})
        return self._json_ok()

#@route('/generateConstraints')
class GenerateConstraints(ConstraintHandler):
    def get(self):
        iterations = int(self.get_argument('iterations'))
        generator_type = self.get_argument('generator')
        if not generator_type in ['planes', 'rectangles', 'quads']:
            return self._json_error("Invalid generator set", 400)

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        smt2interface, generator = self.make_gen(generator_type)
        new_samples, unsat = self.analyze(smt2interface, generator, iterations)

        if len(new_samples) == 0 and len(unsat) == 0:
            return self._json_error("SMT solver did not return an answer")

        samples = self._get_session('samples', {})
        constraints = self._get_session('constraints', [])

        samples.update(new_samples)
        constraints.append(unsat)

        return self.self._json_ok({'sat':_jsonSamples(new_samples), 'unsat':unsat})

class CegarWebSocket(WebSocketHandler, SessionMixin):
    socket_list = {}

    def open(self):
        self.id = uuid.uuid4()
        CegarWebSocket.socket_list[self.id] = self
        #self.session.set('socket_id', self.id)

    def on_close(self):
        del CegarWebSocket.socket_list[self.id]

    def on_message(self, message):
        # TODO: read cancel message
        print("Got unexpected websocket message: {}".format(message))

    def send_samples(self, samples):
        """samples is dictionary point:value"""
        self.write_message({"type":"samples", "data":_jsonSamples(samples)})
        pass

    def send_constraints(self, constraints):
        """constraints is list (poly, safe)"""
        data = [(_jsonPoly(poly), safe) for poly, safe in constraints]
        self.write_message({"type":"constraints", "data":data})

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
        run_tool([config.PARAMETRIC_STORM_COMMAND], True)
        pmcCheckers['pstorm'] = "Parametric Storm"
        print("Found pstorm")
    except:
        pass

    samplers['ratfunc'] = "Rational function"
    try:
        # TODO: Prism sampling not yet supported
        # run_tool([config.PRISM_COMMAND], True)
        # samplers['prism'] = "PRISM"
        # print("Found prism")
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


def make_app():
    settings = {
        'static_path': config.WEB_INTERFACE_DIR,
        'static_url_prefix' : '/ui/',
        'cookie_secret' : "sldfjwlekfjLKJLEAQEWjrdjvsl3807(*&SAd",
        'pycket': {
            'engine': 'redis',
            'storage': {
                'host': 'localhost',
                'port': 6379,
                'db_sessions': 10,
                'db_notifications': 11,
                'max_connections': 2 ** 31,
            },
            'cookies': {
                'expires_days': 120,
            },
        }
    }
    #{
    #    'pycket': {
    #        'engine': 'memcached',
    #        'storage': {
    #            'servers': ('localhost:11211',)
    #        },
    #        'cookies': {
    #            'expires_days': 120,
    #        },
    #    },
    #}

    application = Application([
        (r'/invalidateSession', InvalidateSession),
        (r'/threshold', Threshold),
        (r'/currentResult', CurrentResult),
        (r'/environment', Environment),
        (r'/environments', Environments),
        (r'/results/(.*)', Results),
        (r'/results', Results),
        (r'/uploadPrism', UploadPrism),
        #TODO: ought to be part of result
        (r'/uploadResult', UploadResult),
        (r'/samples', Samples),
        (r'/generateSamples', GenerateSamples),
        (r'/constraints', Constraints),
        (r'/generateConstraints', GenerateConstraints),
        (r'/websocket', CegarWebSocket),
    ], **settings)

    return application

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

    app = make_app()

    if(not cmdargs.server_quiet):
        print("Starting webservice...")

    app.listen(cmdargs.server_port)
    IOLoop.current().start()
