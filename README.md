This README contains instructions for installing and running the Prophesy toolchain. For more information, visit the Prophesy website located at:
http://moves.rwth-aachen.de/research/tools/prophesy
Here, a video tutorial for using the tool can also be found.

Throughout this README, we refer to the Prophesy installation directory as
$PROPHESY_DIR (in the virtual machine, this is /home/cav/prophesy)

The toolset requires at least a 64-bit system. To be able to comfortably run the toolchain, a dualcore system is recommended with 4GB of RAM.

Installation
============

Running benchmarks
==================
In order for you to be able to reproduce our benchmark results, we have included the core of the verification procedure, i.e. the model checker computing the rational function, in the virtual machine. The executable "pstorm" can be found at $PROPHESY_DIR/bin. If you want to run any of the experiments from the paper, please open a terminal (for example by right-clicking the desktop and selecting "Open terminal here" and then changing to the right directory by typing

cd $PROPHESY_DIR/bin

The model checker binary (pstorm) can then be run by invoking

./pstorm [...]

To make things easy, we included a script for each of our benchmark instances that should help reproduce our results. For example, you can check the reachability property on the brp (128,2) instance by running

sh scripts/reach-brp128-2.sh

from the bin directory. Note that it is important to run this script from the /home/prophesy/bin directory, since otherwise the model files and/or executable are not found. The scripts for the other benchmark instances and properties follow a similar naming scheme and can be run in the same fashion. If you want some more statistics, you can manually add "-stats" as an option to the pstorm executable. This will enable more detailed reports on the time used for model building, bisimulation and the actual model checking.
