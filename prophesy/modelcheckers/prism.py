import os
import subprocess
import tempfile

from prophesy.config import configuration
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.input.samplefile import read_samples_file
from prophesy.util import run_tool, ensure_dir_exists, write_string_to_tmpfile
from prophesy.data.samples import SampleDict
from prophesy.adapter.pycarl import Rational
from prophesy.sampling.sampler import Sampler
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
import prophesy.data.range

class PrismModelChecker(ParametricProbabilisticModelChecker, Sampler):
    def __init__(self, location=configuration.get_prism()):
        self.location = location
        self.pctlformula = None
        self.prismfile = None

    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile):
        self.prismfile = prismfile

    def name(self):
        return "prism"

    def version(self):
        args = [self.location, '-version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        # pipe.communicate()
        return pipe.communicate()[0].decode(encoding='UTF-8')

    def get_rational_function(self):
        raise NotImplementedError("This is missing")

    def perform_uniform_sampling(self, variables_and_intervals, samples_per_dimension):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")
        assert len(self.prismfile.parameters) == len(variables_and_intervals[0]), "Number of intervals does not match number of parameters"
        assert samples_per_dimension > 1
        ranges = [prophesy.data.range.create_range_from_interval(interval, samples_per_dimension) for interval in variables_and_intervals[1]]

        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p, r) in zip(variables_and_intervals[0], range_strings)])

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        args = [self.location, self.prismfile.location, pctlpath,
                "-const", const_values_string,
                "-exportresults", resultpath]
        run_tool(args)
        found_parameters, _, samples = read_samples_file(resultpath)
        # compare found parameters with parameter order in prophesy, reorder as needed:
        i = 0
        remap = dict()
        for pname in found_parameters:
            j = 0
            print(pname)
            for var in variables_and_intervals[0]:
                print(var.name)
                if var.name == pname.name:
                    print("match")
                    remap[j] = i
                j = j + 1
            i = i + 1

        assert len(remap) == len(variables_and_intervals[0])
        for (x,y) in remap.items():
            assert x == y, "Remapping not implemented"

        os.unlink(resultpath)
        os.unlink(pctlpath)
        return samples

    def perform_sampling(self, samplepoints):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        samples = SampleDict(self.prismfile.parameters)
        for sample_point in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(var, val) for var, val in sample_point.items()])
            args = [self.location, self.prismfile.location, pctlpath,
                    "-const", const_values_string]
            run_tool(args)
            with open(resultpath) as f:
                f.readline()
                tmp = f.readline()
                assert tmp != None
                assert tmp != ''
                sample_value = Rational(tmp)

            pt = sample_point.get_point(self.prismfile.parameters)
            samples[pt] = sample_value
        os.unlink(resultpath)
        os.unlink(pctlpath)
        return samples
