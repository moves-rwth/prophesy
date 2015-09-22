import os
import errno
import platform
import subprocess
from exceptions.IOError import IOError


def ensure_dir_exists(path):
    """Checks whether the directory exists and creates it if not."""
    assert path is not None
    try:
        os.makedirs(path)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise IOError("Cannot create directory: " + path)
    except BaseException as expecption:
        raise IOError("Path " + path + " seems not valid")


def check_filepath_for_reading(filepath, filedescription_string="file"):
    """Raises exception if file does not exist or is not readable."""
    if not os.path.isfile(filepath):
        raise IOError(filedescription_string + " not found at " + filepath)
    if not os.access(filepath, os.R_OK):
        raise IOError("No read access on " + filedescription_string + ". Location: '" + "'.")


def run_tool(args, quiet=False):
    """Executes a process, returning the `stdout`"""
    pipe = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    if quiet:
        return pipe.communicate()[0]
    else:
        for line in iter(pipe.stdout.readline, ""):
            if not line and pipe.poll() is not None:
                break
            output = line.decode(encoding='UTF-8').rstrip()
            if output != "":
                print("\t * " + output)


def open_file(path):
    """Open file with system-default application.

    Works for Mac OS (`open`) and Linux with `xdg-open`."""
    # TODO: Windows
    platform_specific_open = 'open' if platform.system() == 'Darwin' else 'xdg-open'
    os.system("{open_cmd} {file}".format(open_cmd=platform_specific_open, file=path))


def which(program):
    """
    See http://stackoverflow.com/questions/377017/test-if-executable-exists-in-python/377028#377028
    :param program: String with name of the program
    :return:
    """
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