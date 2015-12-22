import os
import subprocess
import tempfile
from collections import OrderedDict

import config
from modelcheckers.pmc import ProbabilisticModelChecker
from sampling.sampling import read_samples_file
from util import check_filepath_for_reading, run_tool, ensure_dir_exists


class PrismModelChecker(ProbabilisticModelChecker):
    def __init__(self, location=configuration.get(config.EXTERNAL_TOOLS, "prism")):
        self.location = location

    def name(self):
        return "prism"

    def version(self):
        args = [self.location, '-version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        # pipe.communicate()
        return pipe.communicate()[0].decode(encoding='UTF-8')

    def uniform_sample_pctl_formula(self, prism_file, pctl_filepath, ranges):
        assert len(prism_file.parameters) == len(ranges), "Number of value ranges does not match number of parameters"
        check_filepath_for_reading(pctl_filepath, "pctl file")

        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p, r) in zip(prism_file.parameters, range_strings)])

        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)

        args = [self.location, prism_file.location, pctl_filepath,
                "-const", const_values_string,
                "-exportresults", resultpath]
        run_tool(args)
        found_parameters, samples, _ = read_samples_file(resultpath)
        os.unlink(resultpath)
        if found_parameters != prism_file.parameters:
            raise RuntimeError("Prism returns parameters different from the parameters in the prism file")
        return samples

    def sample_pctl_formula(self, prism_file, pctl_filepath, samplepoints):
        check_filepath_for_reading(pctl_filepath, "pctl file")

        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)
        samples = {}
        for pt in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(p, v) for (p, v) in zip(prism_file.parameters, pt)])
            args = [self.location, prism_file.location, pctl_filepath,
                    "-const", const_values_string,
                    "-exportresults", resultpath]
            run_tool(args)
            with open(resultpath) as f:
                f.readline()
                sample_value = float(f.readline())
            samples[pt] = sample_value
        os.unlink(resultpath)
        return OrderedDict(sorted(samples))
