#!/usr/bin/env python3

import configparser
import os
import importlib
from distutils.spawn import find_executable

thisfilepath = os.path.dirname(os.path.realpath(__file__))

def find_tool(name, path=None):
    """
    :param name: Searches for a tool with the given name
    :param path: Optional PATH envirionment where to search
    :return: The location of the path, and an empty string otherwise
    """
    res = find_executable(name, path)
    if res:
        return res
    else:
        return ""

def check_python_api(name):
    """
    :param name:
    :return:
    """
    spec = importlib.util.find_spec(name)
    return spec is not None

def get_initial_web_config(config):
    config_dirs = {}
    config_dirs["server_tmp"] = os.path.join(
        thisfilepath, "/", "tmp", "prophesy_web")
    config_dirs["web_sessions"] = os.path.join(
        config_dirs["server_tmp"], "sessions")
    config_dirs["web_results"] = os.path.join(
        config_dirs["server_tmp"], "results")
    config_dirs["web_examples"] = os.path.join(
        config_dirs["server_tmp"], "examples")
    config["directories"] = config_dirs

def get_initial_config(config):
    # Setup paths
    config_dirs = {}
    config_dirs["tmp"] = os.path.join(thisfilepath, "/", "tmp", "prophesy")
    config_dirs["intermediate_files"] = os.path.join(
        config_dirs["tmp"], "intermediate")
    config_dirs["plots"] = os.path.join(config_dirs["tmp"], "plots")
    config_dirs["custom_path"] = ""
    config["directories"] = config_dirs

    # Setup tool paths
    config_tools = {}
    config_tools["z3"] = find_tool("z3")
    config_tools["isat"] = find_tool("isat")
    config_tools["param"] = find_tool("param")
    config_tools["storm"] = find_tool("storm")
    config_tools["prism"] = find_tool("prism")
    config["external_tools"] = config_tools

    # Setup optional dependencies
    config_deps = {}
    config_deps["stormpy"] = check_python_api("stormpy")
    config_deps["pypdf2"] = check_python_api("PyPDF2")
    config["installed_deps"] = config_deps

    # Setup sampling constants
    config_sampling = {}
    config_sampling["distance"] = str(0.2)
    config_sampling["sampling_threshold_new"] = str(50)
    config["sampling"] = config_sampling

    # Setup constraint constants
    config_constraints = {}
    config_constraints["precision"] = str(0.0001)
    config["constraints"] = config_constraints

def write_initial_config():
    config = configparser.ConfigParser()
    get_initial_config(config)
    path = os.path.join(thisfilepath, "prophesy", "prophesy.cfg")
    print("Writing config to " + path)
    with open(path, 'w') as configfile:
        config.write(configfile)

    config = configparser.ConfigParser()
    get_initial_web_config(config)
    path = os.path.join(thisfilepath, "prophesy_web", "prophesy_web.cfg")
    print("Writing config to " + path)
    with open(path, 'w') as configfile:
        config.write(configfile)

if __name__ == "__main__":
    write_initial_config()
