#!/usr/bin/env python3

import os
import sys
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.data.point import Point
from prophesy.data.samples import SamplePoint, SamplePoints, SampleDict

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '..'))


from prophesy import config
from prophesy.config import configuration

import tempfile
import re
from argparse import ArgumentParser
import shutil
import uuid
import subprocess

from tornado.ioloop import IOLoop
from tornado.web import Application, RequestHandler, RedirectHandler
from tornado.websocket import WebSocketHandler
from tornado.escape import json_decode
from tornado import gen
from pycket.session import SessionMixin
from shapely.geometry.polygon import Polygon

from prophesy.util import ensure_dir_exists
from prophesy.input.resultfile import read_param_result, read_pstorm_result, \
    write_pstorm_result
from prophesy.input.prismfile import PrismFile
from prophesy.modelcheckers.param import ParamParametricModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.smt.smt import setup_smt
from prophesy.smt.isat import IsatSolver
from prophesy.smt.Z3cli_solver import Z3CliSolver
from prophesy.sampling.sampler_ratfunc import RatFuncSampling

from prophesy.sampling.sampling_uniform import UniformSampleGenerator
from prophesy.sampling.sampling_linear import LinearRefinement
from prophesy.sampling.sampling_delaunay import DelaunayRefinement
from prophesy.regions.region_planes import ConstraintPlanes
from prophesy.regions.region_rectangles import ConstraintRectangles
from prophesy.regions.region_quads import ConstraintQuads
from prophesy.regions.region_polygon import ConstraintPolygon

from concurrent.futures import ThreadPoolExecutor
from subprocess import Popen

from pycarl import Rational

default_results = {}

executor = ThreadPoolExecutor(max_workers=1)

if configuration.is_module_available('stormpy'):
    from prophesy.modelcheckers.stormpy import StormpyModelChecker

def _jsonSamples(samples):
    return [{"coordinate" : [float(x), float(y)], "value" : float(v)} for (x, y), v in samples.items()]

def _jsonPoly(polygon):
    if isinstance(polygon, Polygon):
        return _jsonPoly(polygon.exterior)
    return [[pt[0], pt[1]] for pt in polygon.coords]

def getSat(satname):
    if satname == 'z3':
        return Z3CliSolver()
    elif satname == 'isat':
        return IsatSolver()
    else:
        raise RuntimeError("Unknown SAT solver requested")

def getSampler(satname, result):
    if satname == 'ratfunc':
        # Do not use rationals for now
        return RatFuncSampling(result.ratfunc, result.parameters.get_variable_order())
    elif satname == 'prism':
        mc = PrismModelChecker()
        mc.load_model_from_prismfile(result.prism_file)
        return mc
    else:
        raise RuntimeError("Unknown sampler requested")

def getPMC(name):
    if name == 'storm':
        return StormModelChecker()
    #elif name == 'param':
    #    return ParamParametricModelChecker()
    elif name == 'stormpy' and configuration.is_module_available('stormpy'):
        return StormpyModelChecker()
    else:
        raise RuntimeError("Unknown PMC requested")


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

    def _json_ok(self, data = None):
        """Returns JSON OK with formatted data"""
        if data is not None:
            self.write({'status':'ok', 'data':data})
        else:
            self.write({'status':'ok'})

    def _json_canceled(self, data = None):
        """Returns JSON Canceled"""
        self.write({'status':'canceled'})

    def _get_session(self, item, default = None):
        if not item in self.session:
            self.session.set(item, default)
        return self.session.get(item, default)

    def _set_session(self, item, data):
        self.session.set(item, data)
        return data

    def _getResultData(self, name):
        self.setup_results()
        result_files = self._get_session('result_files', {})
        if not name in result_files:
            return None
        try:
            print(result_files[name])
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
                (res_fd, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTS)
                os.close(res_fd)
                results[name] = res_file
                shutil.copyfile(path, res_file)
            self._set_session('result_files', results)
            self._set_session('current_result', next(iter(results.keys()), None))

    def _get_socket(self):
        socket_id = self._get_session('socket_id', None)
        if not socket_id in CegarWebSocket.socket_list:
            return None
        return CegarWebSocket.socket_list[socket_id]

    def open(self):
        self.id = uuid.uuid4()
        self.session.set('socket_id', self.id)

    def _check_canceled(self):
        canceled = self._get_session('canceled', False)
        print("Was canceled? ", canceled)
        if canceled:
            self._set_session('canceled', False)
            return True
        return False

class InvalidateSession(CegarHandler):
    def get(self):
        # Delete temporary files
        result_files = self._get_session('result_files', {})
        for fname in result_files.values():
            try:
                os.unlink(fname)
            except:
                pass
        self.request.session.invalidate()
        return self._json_ok()

class Threshold(CegarHandler):
    def get(self):
        return self._json_ok(self._get_session('threshold', 0.5))

    def put(self):
        threshold = json_decode(self.request.body)
        threshold = float(threshold)
        self._set_session('threshold', threshold)

        # Clear all regions, they are no longer valid
        self._set_session('regions', [])

        return self._json_ok()

    def post(self):
        threshold = self.get_argument('threshold', None)
        threshold = float(threshold)
        self._set_session('threshold', threshold)

        # Clear all regions, they are no longer valid
        self._set_session('regions', [])

        return self._json_ok()

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

class Environment(CegarHandler):
    def get(self):
        return self._json_ok({
                         "pmc"     : self._get_session("pmc", next(iter(ppmcs), None)),
                         "sampler" : self._get_session("sampler", next(iter(samplers), None)),
                         "sat"     : self._get_session("sat", next(iter(satSolvers), None))})

    def post(self):
        pmc = self.get_argument('pmc')
        sampler = self.get_argument('sampler')
        sat = self.get_argument('sat')
        if not pmc in ppmcs:
            print(pmc)
            print(ppmcs)
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

        return self._json_ok()

class Environments(CegarHandler):
    def get(self):
        return self._json_ok({"pmc": list(ppmcs), "samplers":list(samplers), "sat":list(satSolvers)})

class Results(CegarHandler):
    def get(self, name=None):
        self.setup_results()
        result_files = self._get_session('result_files', {})
        if name is None:
            return self._json_ok({k:k for k in result_files.keys()})

        if not name in result_files:
            return self._json_error("Result data not found", 404)

        try:
            print(result_files[name])
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

class UploadPrism(CegarHandler):
    def post(self):
        # Save the files which the user wants to upload
        print("Upload prism ENTRY")
        upload_prism = self.request.files["prism-file"][0]
        if upload_prism is None:
            return self._json_error("Missing PRISM file")

        (prism_fd, prism_path) = tempfile.mkstemp(".prism", dir = config.WEB_RESULTS)
        with os.fdopen(prism_fd, "wb") as prism_f:
            prism_f.write(upload_prism.body)
        prism_files = self._get_session("prism-files", {})
        prism_files[upload_prism.filename] = prism_path
        self._set_session("prism-files", prism_files)

        return self._json_ok();

    def get(self):
        result = {}
        result["prism"] = self._get_session("prism-files", {})
        return self._json_ok(result)

class UploadFormula(CegarHandler):

    def post(self):
        print("Upload PCTL Formula")
        uploaded_pctl_formula = self.get_argument("pctl-formula")
        uploaded_pctl_group = self.get_argument("pctl-group-select")
        uploaded_pctl_name = self.get_argument("pctl-formula-name")
        if uploaded_pctl_group == "addNew" :
            uploaded_pctl_group = self.get_argument("pctl-group-name")
        print(uploaded_pctl_formula)
        print(uploaded_pctl_group)
        print(uploaded_pctl_name)

        pctl_formulas = self._get_session("pctl-formulas", {})
        group_formulas = {}
        if uploaded_pctl_group in pctl_formulas.keys():
            group_formulas = pctl_formulas[uploaded_pctl_group]
        group_formulas[uploaded_pctl_name] = uploaded_pctl_formula

        pctl_formulas[uploaded_pctl_group] = group_formulas
        self._set_session("pctl-formulas", pctl_formulas)
        return self._json_ok()

    def get(self):
        print("Test")

class UploadPctl(CegarHandler):
    def post(self):
        print("Upload pctl ENTRY")
        upload_pctl = self.request.files["pctl-file"][0]
        if upload_pctl is None:
            return self._json_error("Missing PCTL file")

        pctl_content = upload_pctl.body.decode("utf-8").splitlines()
        pctl_formulas = self._get_session("pctl-formulas", {})
        group_formulas = {}
        if upload_pctl.filename in pctl_formulas.keys():
            group_formulas = pctl_formulas[upload_pctl.filename]
        for formula in pctl_content:
            group_formulas[formula] = formula

        pctl_formulas[upload_pctl.filename] = group_formulas
        self._set_session("pctl-formulas", pctl_formulas)
        return self._json_ok()

    def get(self):
        result = {}
        result["pctl"] = self._get_session("pctl-formulas", {})
        return self._json_ok(result)

class RunPrism(CegarHandler):
    def post(self):
        # Run the uploaded prism file with the coosen mctool
        print("Prism CALL")

        # Get the current prism file and save it temporarily
        prism_files = self._get_session("prism-files", {})
        current_prism_file = self.get_argument("prism")
        assert current_prism_file in prism_files
        prism_file = PrismFile(prism_files[current_prism_file])

        # Get the pctl formulas from session and use the ones choosen from UI
        pctl_formulas = self._get_session("pctl-formulas", {})
        current_pctl_group = self.get_argument("pctl_group")
        current_pctl_formula = self.get_argument("pctl_property")
        print("Use Group: {0} with formula {1}".format(current_pctl_group, current_pctl_formula))
        pctl_string = pctl_formulas[current_pctl_group][current_pctl_formula]


        # Special pre-processing if choosen tool is param
        toolname = self.get_argument("mctool")
        assert toolname in ppmcs
        if toolname == "param":
            prism_file.replace_parameter_keyword("param float")
        tool = getPMC(toolname)

        # Try to load the model
        try:
            tool.load_model_from_prismfile(prism_file)
        except Exception as e:
            return self._json_error("Error while loading model: {}".format(e))

        # Try to load the formula
        try:
            tool.set_pctl_formula(pctl_string)
        except Exception as e:
            return self._json_error("Error while loading the formula into the tool: {}".format(e))

        # Run the mctool to evaluate the current ration function
        try:
            result = tool.get_rational_function()
        except Exception as e:
            return self._json_error("Error while computing rational function: {}".format(e))

        # Save the result temporarily
        (res_fd, res_file) = tempfile.mkstemp(".result", "param", config.WEB_RESULTS)
        os.close(res_fd)
        write_pstorm_result(res_file, result)

        result_files = self._get_session('result_files', {})

        if current_prism_file in result_files:
            os.unlink(result_files[current_prism_file])
        result_files[current_prism_file] = res_file
        self._set_session('current_result', current_prism_file)
        self._set_session('result_files', result_files)


        print("Prism run EXIT")
        return self._json_ok(current_prism_file)

class UploadResult(CegarHandler):
    def post(self):
        tool = self.get_argument('result-type')
        upload = self.request.files['result-file'][0]
        # Note: this is not the list of pmcCheckers, but of available result parsers
        if tool not in ['storm', 'param']:
            return self._json_error("Invalid tool selected")
        if upload is None:
            return self._json_error("Missing result file")

        result_files = self._get_session('result_files', {})

        (res_fd, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTS)
        with os.fdopen(res_fd, "wb") as res_f:
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
        (res_fd, res_file) = tempfile.mkstemp(".result", dir = config.WEB_RESULTS)
        os.close(res_fd)
        write_pstorm_result(res_file, result)

        if upload.filename in result_files:
            os.unlink(result_files[upload.filename])
        result_files[upload.filename] = res_file
        self._set_session('current_result', upload.filename)
        self._set_session('result_files', result_files)

        return self._json_ok({"file" : upload.filename})

class PingRedis(CegarHandler):

    def get(self):
        with Popen(["redis-cli", "ping"], stdout=subprocess.PIPE) as proc:
            if proc.stdout.readline() == b'PONG\n':
                return self._json_ok("running")
        return self._json_error("Redis not running")

class Samples(CegarHandler):
    def get(self):
        result = self._getResultData(self._get_session('current_result', None))
        flattenedsamples = _jsonSamples(self._get_session('samples', SampleDict(result.parameters.get_variable_order())))
        return self._json_ok(flattenedsamples)

    def post(self):
        coordinates = json_decode(self.request.body)
        if coordinates is None:
            return self._json_error("Unable to read coordinates", 400)
        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)
        samples = self._get_session('samples', {})
        socket = self._get_socket()
        sampling_interface = getSampler(self._get_session('sampler'), result)

        coordinates = [Point(Rational(x), Rational(y)) for x, y in coordinates]
        sample_points = SamplePoints(coordinates, result.parameters.get_variable_order())
        new_samples = sampling_interface.perform_sampling(sample_points)
        if socket is not None:
            socket.send_samples(new_samples)

        samples.update(new_samples)
        self._set_session('samples', samples)

        return self._json_ok(_jsonSamples(new_samples))

    def put(self):
        coordinate = json_decode(self.request.body)
        try:
            x = Rational(coordinate[0])
            y = Rational(coordinate[1])
        except:
            return self._json_error('Unable to parse coordinate', 400)

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        variables = result.parameters.get_variable_order()
        sampler = getSampler(self._get_session('sampler'), result)
        new_samples = sampler.perform_sampling([SamplePoint({variables[0]:x, variables[1]:y})])
        samples = self._get_session('samples', {})
        samples.update(new_samples)
        return self._json_ok()
        # return _json_ok(_jsonSamples(samples))
        # TODO: redirect?

    def delete(self):
        self._set_session("samples", {})
        return self._json_ok()

class GenerateSamples(CegarHandler):
    @gen.coroutine
    def post(self):
        iterations = int(self.get_argument('iterations'))

        if iterations < 0:
            return self._json_error("Number of iterations must be >= 0", 400)
        threshold = self._get_session('threshold', 0.5)
        generator_type = self.get_argument('generator')
        if not generator_type in ['uniform', 'linear', 'delaunay']:
            return self._json_error("Invalid generator set " + generator_type, 400)

        if generator_type == 'uniform' and iterations < 2:
            return self._json_error("Number of iterations must be >= 2 for uniform generation", 400)

        if iterations == 0:
            # Nothing to do
            return self._json_ok(_jsonSamples({}))

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        socket = self._get_socket()

        samples = self._get_session('samples', SampleDict(result.parameters.get_variable_order()))
        new_samples = {}
        sampling_interface = getSampler(self._get_session('sampler'), result)
        variables = result.parameters.get_variable_order()
        if generator_type == 'uniform':
            intervals = result.parameters.get_variable_bounds()
            samples_generator = UniformSampleGenerator(sampling_interface, variables, samples, intervals, iterations)
        elif generator_type == "linear":
            samples_generator = LinearRefinement(sampling_interface, variables, samples, threshold)
        elif generator_type == "delaunay":
            samples_generator = DelaunayRefinement(sampling_interface, variables, samples, threshold)
        else:
            assert False, "Bad generator"

        def generate_samples(samples_generator, iterations):
            for (generated_samples,_) in zip(samples_generator, range(0, iterations)):
                new_samples.update(generated_samples)
                if socket is not None:
                    socket.send_samples(generated_samples)
                if self._check_canceled():
                    break

            return new_samples

        new_samples = yield executor.submit(generate_samples, samples_generator, iterations)

        samples.update(new_samples)
        self._set_session('samples', samples)
        return self._json_ok(_jsonSamples(new_samples))

class ConstraintHandler(CegarHandler):
    def make_gen(self, type):
        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        samples = self._get_session('samples', SampleDict(result.parameters.get_variable_order()))
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

        #smt2interface.run()

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
                if socket is not None:
                    socket.send_samples({point:value})

            if self._check_canceled():
                break

            iterations -= 1
            if iterations == 0:
                break

        smt2interface.stop()

        return (new_samples, unsat)

class Constraints(ConstraintHandler):
    def get(self):
        constraints = self._get_session('regions', [])
        return self._json_ok(constraints)

    @gen.coroutine
    def post(self):
        #request = json_decode(self.request.body)
        #safe = bool(request['safe'])
        #coordinates = request['coordinates']

        safe = self.get_argument('constr-mode') == "safe"
        coordinates = json_decode(self.get_argument('coordinates'))
        if coordinates is None:
            return self._json_error("Unable to read coordinates", 400)
        coordinates = [(float(x), float(y)) for x, y in coordinates]
        if coordinates[0] == coordinates[-1]:
            # Strip connecting point if any
            coordinates = coordinates[:-1]

        smt2interface, generator = self.make_gen("poly")
        generator.add_polygon(Polygon(coordinates), safe)
        new_samples, unsat = yield executor.submit(self.analyze, smt2interface, generator)

        if len(new_samples) == 0 and len(unsat) == 0:
            return self._json_error("SMT solver did not return an answer")

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)
        samples = self._get_session('samples', SampleDict(result.parameters.get_variable_order()))
        constraints = self._get_session('regions', [])

        samples.update(new_samples)
        constraints += unsat

        self._set_session('samples', samples)
        self._set_session('regions', constraints)

        return self._json_ok({'sat':_jsonSamples(new_samples), 'unsat':unsat})
        # TODO: redirect?

    def delete(self):
        self._set_session('regions', [])
        return self._json_ok()

class GenerateConstraints(ConstraintHandler):
    @gen.coroutine
    def post(self):
        iterations = int(self.get_argument('iterations'))
        generator_type = self.get_argument('generator')
        if not generator_type in ['planes', 'rectangles', 'quads']:
            return self._json_error("Invalid generator set", 400)

        result = self._getResultData(self._get_session('current_result', None))
        if result is None:
            return self._json_error("Unable to load result data", 500)

        smt2interface, generator = self.make_gen(generator_type)
        new_samples, unsat = yield executor.submit(self.analyze, smt2interface, generator, iterations)

        if len(new_samples) == 0 and len(unsat) == 0:
            return self._json_error("SMT solver did not return an answer")

        samples = self._get_session('samples', {})
        # Clear all regions, resumption not supported (yet)
        constraints = [] #self._get_session('regions', [])

        samples.update(new_samples)
        constraints += unsat

        self._set_session('samples', samples)
        self._set_session('regions', constraints)

        return self._json_ok({'sat': _jsonSamples(new_samples), 'unsat': unsat})


class CegarWebSocket(WebSocketHandler, SessionMixin):
    socket_list = {}

    def open(self):
        self.id = uuid.uuid4()
        CegarWebSocket.socket_list[self.id] = self
        self.session.set('socket_id', self.id)

    def on_close(self):
        del CegarWebSocket.socket_list[self.id]

    def on_message(self, message):
        if message == 'cancel':
            print("Received cancel operation")
            self.session.set('canceled', True)
        else:
            print(("Got unexpected websocket message: {}".format(message)))

    def send_samples(self, samples):
        """samples is dictionary point:value"""
        self.write_message({"type": "samples", "data": _jsonSamples(samples)})
        pass

    def send_constraints(self, constraints):
        """regions is list (poly_list, safe)"""
        self.write_message({"type": "regions", "data": constraints})


class Configuration(CegarHandler):

    # Handler for the Webconfiguartion interface

    # Reads the Configuratuion from the config-file
    def get(self, section=None, key=None):
        if section:
            if key:
                return self._json_ok(configuration.get(section, key))
        return self._json_ok(configuration.getAll())

    # Sets the given configuartions from the Webinterface (JSON)
    def put(self):
        pass

    # Sets the given configurations from the Webinterface (HTTP)
    def post(self, section=None, key=None):
        if section:
            if key:
                configuration.set(section, key, str(self.get_argument("data")))
                configuration.updateConfigurationFile()
                return self._json_ok()
        return self._json_error()

def initEnv():
    # Check available model checkers, solvers and various other regions
    # and adjust capabilities based on that
    global satSolvers, samplers, ppmcs
    satSolvers = configuration.getAvailableSMTSolvers()
    samplers = configuration.getAvailableSamplers()
    ppmcs = configuration.getAvailableParametricMCs()

    # Preload some result files for easy startup
    print("Loading default result files...")
    rat_path = configuration.get(config.DIRECTORIES, 'web_examples')
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


def make_app(hostname):
    settings = {
        'static_path': config.configuration.get(config.DIRECTORIES, "web_interface"),
        'static_url_prefix' : '/ui/',
        'cookie_secret' : "sldfjwlekfjLKJLEAQEWjrdjvsl3807(*&SAd",
        'pycket': {
            'engine': 'redis',
            'storage': {
                'host': hostname,
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
        (r"/", RedirectHandler, dict(url="ui/index.html")),
        (r"/files", RedirectHandler, dict(url="ui/filemanager.html")),
        (r"/configuration", RedirectHandler, dict(url="ui/configuration.html")),
        (r'/invalidateSession', InvalidateSession),
        (r'/threshold', Threshold),
        (r'/currentResult', CurrentResult),
        (r'/environment', Environment),
        (r'/environments', Environments),
        (r'/results/(.*)', Results),
        (r'/results', Results),
        (r'/uploadPrism', UploadPrism),
        (r'/uploadPctl', UploadPctl),
        (r'/uploadFormula', UploadFormula),
        (r'/runPrism', RunPrism),
        #TODO: ought to be part of result
        (r'/uploadResult', UploadResult),
        (r'/samples', Samples),
        (r'/generateSamples', GenerateSamples),
        (r'/regions', Constraints),
        (r'/generateConstraints', GenerateConstraints),
        (r'/websocket', CegarWebSocket),
        (r'/config/(.*)/(.*)$', Configuration),
        (r'/config', Configuration),
        (r'/checkRedis', PingRedis)
    ], **settings)

    return application


def parse_cli_args():
    parser = ArgumentParser(description='Start a webservice for ' + config.TOOLNAME)
    parser.add_argument('--server-port', type=int, help='the port the server listens on', default=4242)
    parser.add_argument('--server-host', help="server host name", default="localhost")
    parser.add_argument('--server-debug', type=bool, help='run the server in debug mode', default=True)
    parser.add_argument('--server-quiet', type=bool, help='run the server in quiet mode', default=False)
    return parser.parse_args()


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    ensure_dir_exists(configuration.get(config.DIRECTORIES, "web_sessions"))
    ensure_dir_exists(config.WEB_RESULTS)
    ensure_dir_exists(configuration.get(config.DIRECTORIES, "web_examples"))

    session_opts = {
        'session.type': 'file',
        'session.data_dir': config.configuration.get(config.DIRECTORIES, "web_sessions"),
        'session.auto': True,
        'session.invalidate_corrupt':False
    }

    initEnv()

    app = make_app(cmdargs.server_host)

    if(not cmdargs.server_quiet):
        print("Starting webservice...")

    app.listen(cmdargs.server_port)
    IOLoop.current().start()
