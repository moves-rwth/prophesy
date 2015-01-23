import os
thisfilepath = os.path.dirname(os.path.realpath(__file__))

VERSION = [0, 3, 0]

AUTHORS = ["Florian Corzilius", "Christian Dehnert", "Nils Jansen", "Sebastian Junges", "Matthias Volk"]
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

# external tools
Z3_COMMAND = "z3"
SMTRAT_COMMAND = "smtrat"
PARAMETRIC_STORM_COMMAND = "pstorm"
PARAM_COMMAND = "param"
PRISM_COMMAND = "prism"

# epsilon for constraint generation
EPS = 0.0001
