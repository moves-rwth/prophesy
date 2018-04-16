from prophesy.config import modules

# Only import if stormpy module is available
if modules.is_module_available("gurobipy"):
    from gurobipy import *