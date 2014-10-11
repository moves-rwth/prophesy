import re

def findParametersInPrismFile(path, replace_keyword=None):
    if replace_keyword == None:
        with open(path, 'r') as f:
            inputstring = f.read()
            parameters = re.findall("^const double (.*\s*);", inputstring, re.MULTILINE)
            print(parameters)
            return parameters
    else:
        raise NotImplementedError


class PrismFile():
    
    def __init__(self, location):
        self.location = location
        self.parameters = findParametersInPrismFile(location)
        
        
        


         