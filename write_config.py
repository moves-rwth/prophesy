#!/usr/bin/env python3

import configparser
import os
import sys
import importlib
import logging
from distutils.spawn import find_executable

thisfilepath = os.path.dirname(os.path.realpath(__file__))


def is_executable(path):
    """
    Check if the path is an executable.
    :param path: path.
    :return: True iff the path is an executable.
    """
    return os.path.isfile(path) and os.access(path, os.X_OK)


def find_tool(name, path=None):
    """
    Search for a tool with the given name.
    :param name: Tool name.
    :param path: Optional path to search recursively.
    :return: The location of the tool, and an empty string otherwise
    """
    res = find_executable(name)
    if res:
        return res

    if path is not None:
        # Search manually in the given path
        if sys.version_info[1] >= 5:
            # Python >= 3.5
            import glob
            for file in glob.iglob(os.path.join(path, "**", name), recursive=True):
                if is_executable(file):
                    return file
        else:
            # Python <= 3.4
            import fnmatch
            for root, dirnames, filenames in os.walk(path):
                for filename in fnmatch.filter(filenames, name):
                    file = os.path.join(root, filename)
                    if is_executable(file):
                        return file

    return ""


def check_python_api(name):
    """
    Check if the required python module is present.
    :param name: Name of the python api.
    :return: True iff the api is present.
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


def get_initial_config(config, search_path):
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
    config_tools["z3"] = find_tool("z3", search_path)
    config_tools["isat"] = find_tool("isat", search_path)
    config_tools["yices"] = find_tool("yices-smt2", search_path)
    config_tools["param"] = find_tool("param", search_path)
    config_tools["storm"] = find_tool("storm", search_path)
    config_tools["storm-pars"] = find_tool("storm-pars", search_path)
    config_tools["prism"] = find_tool("prism", search_path)
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
    config["constraints"] = config_constraints

    config_smt = {}
    config_smt["timeout"] = str(10)
    config["smt"] = config_smt


def write_initial_config(search_path = None):
    print("Write config with search path {}".format(search_path))
    config = configparser.ConfigParser()
    get_initial_config(config, search_path)
    path = os.path.join(thisfilepath, "prophesy", "prophesy.cfg")
    logging.info("Writing config to " + path)
    with open(path, 'w') as configfile:
        config.write(configfile)

    config = configparser.ConfigParser()
    get_initial_web_config(config)
    path = os.path.join(thisfilepath, "prophesy_web", "prophesy_web.cfg")
    logging.info("Writing config to " + path)
    with open(path, 'w') as configfile:
        config.write(configfile)


if __name__ == "__main__":
    write_initial_config()
