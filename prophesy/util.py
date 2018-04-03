import os
import errno
import platform
import subprocess
import tempfile
import configparser
import logging

from prophesy.exceptions.configuration_error import ConfigurationError

logger = logging.getLogger(__name__)


class Configuration:
    """
    Configuration for prophesy.
    """

    def __init__(self, config_file):
        """
        Constructor.
        :param config_file: Path to config file.
        """
        self._config = configparser.ConfigParser()
        self._import_from_file(config_file)
        self._file_path = config_file
        self.modified = False

    def _import_from_file(self, config_file):
        """
        Import configuration from file.
        :param config_file: Configuration file.
        """
        parsed_files = self._config.read(config_file)
        if len(parsed_files) == 0:
            raise ConfigurationError(
                "Unable to read configuration file '{}'".format(config_file))
        self._importedFrom = config_file

    def check_existence(self, section, key):
        """
        Check if the given key exists in the configuration and raise a ConfigurationError if not.
        :param section: Section.
        :param key: Key.
        """
        if section not in self._config:
            raise ConfigurationError("Cannot find section {} in file {}".format(section, self._file_path))

        if key not in self._config[section]:
            raise ConfigurationError(
                "Cannot find key {} in section {} in file {}".format(key, section, self._file_path))

    def get(self, section, key):
        """
        Get config value for given key.
        :param section: Section.
        :param key: Key.
        :return: Config value.
        """
        self.check_existence(section, key)
        return self._config[section][key]

    def get_boolean(self, section, key):
        """
        Get config value as boolean.
        :param section: Section.
        :param key: Key.
        :return: Config value as boolean.
        """
        self.check_existence(section, key)
        return self._config.getboolean(section, key)

    def get_float(self, section, key):
        """
        Get config value as float.
        :param section: Section.
        :param key: Key.
        :return: Config value as float.
        """
        self.check_existence(section, key)
        return self._config.getfloat(section, key)

    def get_int(self, section, key):
        """
        Get config value as integer.
        :param section: Section.
        :param key: Key.
        :return: Config value as integer.
        """
        self.check_existence(section, key)
        return self._config.getint(section, key)

    def get_all(self):
        """
        Get all entries of the configuration.
        :return: Dict with all entries.
        """
        result = {}
        for section in self._config.sections():
            result[section] = dict(self._config.items(section))
        return result

    def set(self, section, key, value):
        """
        Set config entry.
        :param section: Section.
        :param key: Key.
        :param value: New value.
        """
        logger.debug("Update config: / %s / %s = %s", section, key, value)
        self._config.set(section, key, value)
        self.modified = True

    def update_configuration_file(self):
        """
        Write configuration file again.
        """
        logger.info("Update config file %s", self._importedFrom)
        with open(self._importedFrom, 'w') as f:
            self._config.write(f)
        self.modified = False


def ensure_dir_exists(path):
    """
    Check whether the directory exists and create it if not. Raises an IOError if not successful.
    :param path: Directory path.
    """
    assert path is not None
    try:
        os.makedirs(path)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise IOError("Cannot create directory: " + path)
    except BaseException:
        raise IOError("Path " + path + " seems not valid")


def check_filepath_for_reading(filepath, filedescription_string="file"):
    """
    Check if the given path can be read. Raises an IOError otherwise.
    :param filepath: Path.
    :param filedescription_string: Type of path (file/dir).
    """
    if not os.path.isfile(filepath):
        raise IOError(filedescription_string + " not found at " + filepath)
    if not os.access(filepath, os.R_OK):
        raise IOError("No read access on " + filedescription_string + ". Location: '" + "'.")


def run_tool(args, quiet=False, outputfile=None):
    """
    Executes a process.
    :param args: CLI arguments to execute.
    :param quiet: If false the output is logged.
    :param outputfile: Path for saving output.
    :return: Stdout of process or exitcode.
    """
    logger = logging.getLogger("External Tool")
    pipe = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    if quiet and outputfile is None:
        result = pipe.communicate()[0].decode(encoding='UTF-8')
        pipe.terminate()
        return result
    else:
        for line in iter(pipe.stdout.readline, ""):
            if not line and pipe.poll() is not None:
                break
            output = line.decode(encoding='UTF-8').rstrip()
            if not quiet and output != "":
                logger.debug("\t * " + output)
            if outputfile is not None:
                write_string_to_file(outputfile, output + "\n", append=True)
    pipe.terminate()
    return pipe.returncode


def open_file(path):
    """
    Open file with system-default application.
    Works for Mac OS (`open`) and Linux with `xdg-open`.
    :param path: Path.
    """
    platform_specific_open = 'open' if platform.system() == 'Darwin' else 'xdg-open'
    os.system("{open_cmd} {file}".format(open_cmd=platform_specific_open, file=path))


def write_string_to_file(path, string, append=False):
    """
    Write string to file.
    :param path: File where we want to put the string.
    :param string: New content.
    :param append: If True, append to file, else overwrite.
    """
    with open(path, 'a' if append else 'w') as f:
        f.write(string)


def write_string_to_tmpfile(string):
    """
    Write string to temporary file.
    :param string: New content.
    :return: The path to the temporary file.
    """
    _, path, = tempfile.mkstemp(suffix=".pctl", text=True)
    write_string_to_file(path, string)
    return path


def which(program):
    """
    Check if executable exists and return its path.
    See http://stackoverflow.com/questions/377017/test-if-executable-exists-in-python/377028#377028
    :param program: String with name of the program.
    :return: Path to program or None if not found.
    """
    from prophesy import config
    from prophesy.config import configuration

    def is_exe(path_exe):
        return os.path.isfile(path_exe) and os.access(path_exe, os.X_OK)

    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep) + configuration.get(config.DIRECTORIES, "custom_path").split(
                ","):
            path = path.strip('"')
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file

    return None
