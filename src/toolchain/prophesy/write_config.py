import configparser
import os
thisfilepath = os.path.dirname(os.path.realpath(__file__))
home = os.path.expanduser("~")


def write_initial_config(path):
    print("Writing config to " + path)
    config = configparser.ConfigParser()
    config_dirs = {}
    config_dirs["tmp"] =  os.path.join(thisfilepath, "../tmp/")
    config_dirs["intermediate_files"] = os.path.join(config_dirs["tmp"], "intermediate")
    config_dirs["plots"] = os.path.join(config_dirs["tmp"], "plots")
    config_dirs["server_tmp"] = os.path.join(thisfilepath, "../tmp/web")
    config_dirs["web_sessions"] = os.path.join(config_dirs["server_tmp"], "sessions")
    config_dirs["web_results"] = os.path.join(config_dirs["server_tmp"], "results")
    config_dirs["web_interface"] = os.path.join(thisfilepath, "../../webinterface")
    config_dirs["web_examples"] = os.path.join(config_dirs["server_tmp"], "examples")
    config_dirs["custom_path"] = ""
    config["directories"] = config_dirs
    config_tools = {}
    config_tools["z3"] = "z3"
    config_tools["isat"] = "isat"
    config_tools["smtrat"] = "smtrat"
    config_tools["param"] = ""
    config_tools["storm"] = os.path.join(home, "storm")
    config["external_tools"] = config_tools

    #
    config_sampling = {}
    config_sampling["distance"] = str(0.2)
    config_sampling["sampling_threshold_new"] = str(50)
    config["sampling"] = config_sampling

    with open(path, 'w') as configfile:
        config.write(configfile)

if __name__ == "__main__":
    write_initial_config(os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy.cfg"))