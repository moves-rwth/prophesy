import os

VERSION = [0, 3, 0]

AUTHORS = ["Florian Corzilius", "Christian Dehnert", "Nils Jansen", "Sebastian Junges", "Matthias Volk"]
SUPPORT = ["Nils Jansen", "Sebastian Junges"]
TOOLNAME = "Cool Toolname"

thisfilepath =  os.path.dirname(os.path.realpath(__file__))


# temporary directories, change if you want the files to reside elsewhere.
TMP_DIR = os.path.join(thisfilepath, "../tmp/")
WEBSESSIONS_DIR = os.path.join(TMP_DIR, "web/sessions/")
INTERMEDIATE_FILES_DIR = os.path.join(TMP_DIR, "web/intermediate/")

# directory with webinterface
WEB_INTERFACE_DIR = os.path.join(thisfilepath, "../../webinterface/")

# external tools
Z3_COMMAND = "z3"
SMTRAT_COMMAND = "smtrat"
PARAMETRIC_STORM_COMMAND = "pstorm"
PARAM_COMMAND = "param"
PRISM_COMMAND = "prism"



#CONSTRAINT_GENERATION_COMMAND = "./polyCreator.py"