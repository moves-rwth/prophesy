from modelcheckers.ppmc import *
import subprocess

class ProphesyParametricModelChecker(ParametricProbablisticModelChecker):
    def __init__(self, location):
        self.location = location
    
    def name(self):
        return "pstorm"
    
    def version(self):
        args = [self.location, '--version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        #pipe.communicate()
        outputstr = pipe.communicate()[0].decode(encoding='UTF-8')
        output = outputstr.split("\n")
        return output[len(output)-2]
    
    
    def get_rational_function(self, prism_filepath, pctl_filepath): 
        check_filepath_for_reading(prism_filepath, "Prism file")
        check_filepath_for_reading(pctl_filepath, "pctl file")
        
        #get the pctl string from the file.
        pctl_formulas = parse_pctl_file(pctl_filepath)
        if len(pctl_formulas) == 0:
            raise 
        if len(pctl_formulas) > 1:
            warnings.warn("pctl file contains more than one formula. {0} only takes the first.".format(self.name()))
        
        #TODO make sure the pctl formula is supported.
        
        #create a temporary file for the result.
        resultfile = tempfile.mkstemp(text=True)
        resultfile[0].close()
        
        args = [self.location,
                '--symbolic', prism_file,
                '--pctl', str(pctl_formulas.front),
                '--parametric:resultfile', resultfile[1] ]
        
        parse_result_file(resultfile[1])
       
        #/pstorm --symbolic examples/pdtmc/brp/brp_32-4.pm --pctl "P=? [F target]"
        
        
        