import os
import errno
import subprocess


def ensure_dir_exists(path):
    """Checks whether the directory exists and creates it if not."""
    try:
        os.makedirs(path)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise


def check_filepath_for_reading(filepath, filedescription_string="file"):
    """Raises exception if file does not exist or is not readable."""
    if not os.path.isfile(filepath):
        raise IOException(filedescription_string + " not found at " + filepath)
    if not os.access(filepath, os.R_OK):
        raise IOException("No read access on " + filedescription_string + ". Location: '" + "'.")

def run_tool(args, quiet=False):
    """Executes a process, returning the `stdout`"""
    pipe = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    if quiet:
        return pipe.communicate()[0]
    else:
        for line in iter(pipe.stdout.readline, ""):
            if not line and pipe.poll() != None:
                break
            output = line.decode(encoding='UTF-8').rstrip()
            if output != "":
                print("\t * " + output)

