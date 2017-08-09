from prophesy.config import configuration

# Only import if stormpy module is available
if configuration.is_module_available("stormpy"):
    from prophesy.adapter.pycarl import *
    import stormpy
    from stormpy import *
    import stormpy.info as info
    import stormpy.logic as logic

    if not stormpy._config.storm_with_pars:
        raise ImportError("Stormpy was built without necessary parametric module.")
    import stormpy.pars as pars
