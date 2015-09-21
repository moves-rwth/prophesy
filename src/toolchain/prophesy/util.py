import os
import errno
import subprocess
from exceptions.IOError import IOError

def ensure_dir_exists(path):
    assert path != None
    try:
        os.makedirs(path)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise IOError("Cannot create directory: " + path)
    except BaseException as expecption:
        raise IOError("Path " + path + " seems not valid")


def check_filepath_for_reading(filepath, filedescription_string = "file"):
    if not os.path.isfile(filepath):
        raise IOError(filedescription_string + " not found at " + filepath)
    if not os.access(filepath, os.R_OK):
        raise IOError("No read access on " + filedescription_string + ". Location: '" + "'.")

def run_tool(args, quiet = False):
    pipe = subprocess.Popen(args, stdout = subprocess.PIPE, stderr = subprocess.STDOUT)

    if(quiet):
        return pipe.communicate()[0]
    else:
        for line in iter(pipe.stdout.readline, ""):
            if not line and pipe.poll() != None:
                break
            output = line.decode(encoding = 'UTF-8').rstrip()
            if output != "":
                print("\t * " + output)

