# import tempfile
# from config import configuration
# import config
# import subprocess
# import os
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
# from util import check_filepath_for_reading, run_tool, ensure_dir_exists
# from input.resultfile import read_param_result

class ParamParametricModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self):
        NotImplementedError("Param is currently not supported" )


# class ParamParametricModelChecker(ParametricProbablisticModelChecker):
#     def __init__(self, location=configuration.get_param()):
#         self.location = location
#
#     def name(self):
#         return "param"
#
#     def version(self):
#         args = [self.location, "--help"]
#         pipe = subprocess.Popen(args, stdout = subprocess.PIPE)
#         # pipe.communicate()
#         outputstr = pipe.communicate()[0].decode(encoding = 'UTF-8')
#         output = outputstr.split("\n")
#         return output[2][1:-1].strip()
#
#     def get_rational_function(self, prism_file, pctl_filepath):
#         check_filepath_for_reading(pctl_filepath, "pctl file")
#
#         # create a temporary file for the result. Note: Param will create its own file
#         # based on given prefix, so need to unlink twice
#         ensure_dir_exists(configuration.get_intermediate_dir())
#         (_, resultfile) = tempfile.mkstemp(suffix = ".txt", dir = configuration.get_intermediate_dir()), text = True)
#         os.unlink(resultfile)
#
#         args = [self.location,
#                 prism_file.location,
#                 pctl_filepath,
#                 "--result-file", resultfile,
#                 "--no-startup-message"]
#         run_tool(args, True)
#
#         # Param adds ".out" extension
#         resultfile = resultfile + ".out"
#         paramResult = read_param_result(resultfile)
#         os.unlink(resultfile)
#         # Param also generates a states and regions file, delete those too
#         os.unlink("states")
#         os.unlink("regions.tex")
#         return paramResult
