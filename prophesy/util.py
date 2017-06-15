import os
import errno
import platform
import subprocess
import tempfile
import configparser
import logging

from prophesy.exceptions.configuration_error import ConfigurationError

class Configuration():
    def __init__(self, config_file):
        self._config = configparser.ConfigParser()
        self._importFromFile(config_file)
        self.modified = False

    def _importFromFile(self, config_file):
        parsed_files = self._config.read(config_file)
        if len(parsed_files) == 0:
            raise ConfigurationError(
                "Unable to read configuration file '{}'".format(config_file))
        self._importedFrom = config_file

    def get(self, section, key):
        if section not in self._config:
            raise ConfigurationError("Cannot find section {}".format(section))

        if key not in self._config[section]:
            raise ConfigurationError(
                "Cannot find key {} in section {}".format(key, section))
        return self._config[section][key]

    def getboolean(self, section, key):
        if section not in self._config:
            raise ConfigurationError("Cannot find section {}".format(section))

        if key not in self._config[section]:
            raise ConfigurationError(
                "Cannot find key {} in section {}".format(key, section))
        return self._config.getboolean(section, key)

    def getAll(self):
        result = {}
        for section in self._config.sections():
            result[section] = dict(self._config.items(section))
        return result

    def set(self, section, key, value):
        self._config.set(section, key, value)
        self.modified = True

    def updateConfigurationFile(self):
        with open(self._importedFrom, 'w') as f:
            self._config.write(f)
        self.modified = False


def ensure_dir_exists(path):
    """Checks whether the directory exists and creates it if not."""
    assert path is not None
    try:
        os.makedirs(path)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise IOError("Cannot create directory: " + path)
    except BaseException:
        raise IOError("Path " + path + " seems not valid")


def check_filepath_for_reading(filepath, filedescription_string="file"):
    """Raises exception if file does not exist or is not readable."""
    if not os.path.isfile(filepath):
        raise IOError(filedescription_string + " not found at " + filepath)
    if not os.access(filepath, os.R_OK):
        raise IOError("No read access on " + filedescription_string + ". Location: '" + "'.")


def run_tool(args, quiet=False, logfile=None):
    """
    Executes a process,
    :returns: the `stdout`
    """
    logger = logging.getLogger("External Tool")
    pipe = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    if quiet and logfile is None:
        return pipe.communicate()[0]
    else:
        for line in iter(pipe.stdout.readline, ""):
            if not line and pipe.poll() is not None:
                break
            output = line.decode(encoding='UTF-8').rstrip()
            if not quiet and output != "":
                logger.debug("\t * " + output)
            if logfile is not None:
                write_string_to_file(logfile, output + "\n", append=True)

    return pipe.returncode

def open_file(path):
    """Open file with system-default application.

    Works for Mac OS (`open`) and Linux with `xdg-open`."""
    platform_specific_open = 'open' if platform.system() == 'Darwin' else 'xdg-open'
    os.system("{open_cmd} {file}".format(open_cmd=platform_specific_open, file=path))


def write_string_to_file(path, string, append=False):
    """
    :param path: File where we want to put the string
    :param string: New content
    :param append: If True, append to file, else overwrite
    :return:
    """
    with open(path, 'a' if append else 'w') as f:
        f.write(string)

def write_string_to_tmpfile(string):
    """
    :param string:
    :return: The path to the temporary file
    """
    _, path, = tempfile.mkstemp(suffix=".pctl", text=True)
    write_string_to_file(path, string)
    return path

def which(program):
    """
    See http://stackoverflow.com/questions/377017/test-if-executable-exists-in-python/377028#377028
    :param program: String with name of the program
    :return:
    """
    from prophesy import config
    from prophesy.config import configuration

    def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep) + configuration.get(config.DIRECTORIES, "custom_path").split(","):
            path = path.strip('"')
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file

    return None