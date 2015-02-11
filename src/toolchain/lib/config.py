import os
thisfilepath = os.path.dirname(os.path.realpath(__file__))

VERSION = [0, 3, 0]

AUTHORS = ["Harold Bruintjes", "Florian Corzilius", "Christian Dehnert", "Nils Jansen", "Sebastian Junges", "Matthias Volk"]
SUPPORT = ["Nils Jansen", "Sebastian Junges"]
TOOLNAME = "Prophesy"

# temporary directories, change if you want the files to reside elsewhere.
TMP_DIR = os.path.join(thisfilepath, "../tmp/")
INTERMEDIATE_FILES_DIR = os.path.join(TMP_DIR, "intermediate")
PLOT_FILES_DIR = os.path.join(TMP_DIR, "plots")
WEB_SESSIONS_DIR = os.path.join(TMP_DIR, "web/sessions")
WEB_RESULTFILES_DIR = os.path.join(TMP_DIR, "web/results")

# directory with webinterface
WEB_INTERFACE_DIR = os.path.join(thisfilepath, "../../webinterface/")

TOOL_DIR = "/home/prophesy/bin"
EXAMPLES_DIR = "/home/prophesy/examples"

# external tools
Z3_COMMAND = os.path.join(TOOL_DIR, "z3")
SMTRAT_COMMAND = os.path.join(TOOL_DIR, "smtrat")
PARAMETRIC_STORM_COMMAND = os.path.join(TOOL_DIR, "pstorm")
PARAM_COMMAND = os.path.join(TOOL_DIR, "param")
PRISM_COMMAND = os.path.join(TOOL_DIR, "prism")

# epsilon for constraint generation
EPS = 0.0001

SAMPLING_DISTANCE = 0.2
SAMPLING_THRESHOLD_NEW = 50

#CONSTRAINT_GENERATION_COMMAND = "./polyCreator.py"
