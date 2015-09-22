from config import configuration


def check_available_smtsolvers():
    smtsolvers = []
    try:
        which(configuration.get(config.EXTERNAL_TOOLS, "z3"))
        smtsolvers.append("z3")
        print("Found z3")
    except:
        pass
    try:
        run_tool(configuration.get(config.EXTERNAL_TOOLS, "smtrat"), True)
        smtsolvers.append("smtrat")
        print("Found smtrat")
    except:
        pass
    return smtsolvers

def check_available_pmcs():


def check_available_tools():
    try:
        run_tool([configuration.get(config.EXTERNAL_TOOLS, "param")], True)
        ppmcCheckers['param'] = "Param"
        print("Found param")
    except:
        pass
    try:
        run_tool([configuration.get(config.EXTERNAL_TOOLS, "storm")], True)
        ppmcCheckers['pstorm'] = "Parametric Storm"
        print("Found pstorm")
    except:
        pass

    samplers['ratfunc'] = "Rational function"
    samplers['ratfunc_float'] = "Rational function (float)"
    samplers['carl'] = "Carl library"


    try:
        # TODO: Prism sampling not yet supported
        # run_tool([config.PRISM_COMMAND], True)
        # samplers['prism'] = "PRISM"
        # print("Found prism")
        pass
    except:
        pass


    if len(ppmcCheckers) == 0:
        raise RuntimeError("No model checkers in environment")
    if len(samplers) == 0:
        # The astute programmer can see that this should never happen
        raise RuntimeError("No samplers in environment")
    if len(smtsolvers) == 0:
        raise RuntimeError("No SAT solvers in environment")