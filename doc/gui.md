
================
Running tool GUI
================
In order to use the web-frontend of the tool, please first start the webservice by opening a terminal, change the directory with

cd $PROPHESY_DIR/prophesy

executing

./run_server.sh

and then wait for the line "Starting webservice..." to appear. Then, you can access the frontend via the browser. To do so, go to the URL
http://localhost:4242/

You can then use the GUI as illustrated by the video on the website ( http://moves.rwth-aachen.de/research/tools/prophesy ). The workflow of the GUI follows three steps: Loading a model, sampling in the search space, and calculation constraints.

Loading a model:
At the top right corner, three tabs are available:
* Upload PRISM: Use this to load a PRISM model file and corresponding PCTL formula (these are contained in the examples.zip package, in the directory examples/pdtmc). After selecting both files, select the tool to use to calculate the rational function. This can be either Parametric Storm (pstorm) or Param. Note: To use param, PRISM files with a slightly altered syntax have to be used (consult the Param documentation for details). These can be found in the examples/param directory.
Press the 'Upload' button to submit the files and calculate the resulting rational function. When this is done, the results are automatically loaded.
* Upload result: Use this to upload a previously calculated rational function (for instance after running benchmarks). As there is a slight difference in syntax, make sure to select the tool that was used to generate the file. Submit the file using the 'Upload' button, the results are then loaded.
* Select results: Any previously submitted models, plus a few standard examples, can be selected from a list presented in this tab. This allows one to quickly switch between models and continue analysis after closing the browser.

Sampling the search space:
The get an idea of the effect of the parameters on the final probability, and to aid constraint generation, the search space can be sampled. Two tabs are available:
* Manual sampling: Enabling manual sampling on this tab allows one to click in the plot to pick points where the rational function should be sampled. After selecting these points, the 'Check new' will sample these points. Values below the threshold are rendered green, values above are red.
* Auto sampling: Sample points can be generated automatically as well. This is done by generating a uniform grid of points first (the 'Sampling number' parameter), followed by refining points that are close to the threshold (the 'Number of iterations' parameter). Finally, two methods to find points close to the threshold are provided: Linear interpolation and Delaunay triangulation. It strongly depends on the model which performs better, so if one does not function satisfactory try the other. The 'Go' button will then calculate the samples. Note: Doing so will clear any previously determined sample points.

Generating constraints:
Finally, to prove that parts of the search space are either safe (below the threshold) or bad (above the threshold), constraints can be generated that capture subsets of the search space. Again, two methods are available, manual and automatic:
* Manual Constraints: Enabling the option on this tab allows one to define a polygon in the plot by drawing its vertices. This polygon is then transformed into a constraint (or multiple if necessary) which can then be checked to be either safe of bad. To select either 'Check for safe' or 'Check for bad', and submit the constraint with 'Check new'. To start drawing a new polygon before submitting the current, press 'Clear current'.
* Auto Constraints: This tab presents a list of algorithms to generate constraints automatically. They are

They are described in more detail in the Prophesy paper. After selecting the appropriate algorithm, constraints generated by clicking 'Generate'.

For both manual and automatic constraint analysis, Z3 is used. Performance varies greatly depending on the input model and constraint shape. If analysis terminated without result, try changing the parameters and (in case of manual constraints) shape and try again.

Changing settings:
Throughout using the GUI, the 'Threshold' setting can be adjusted as required. Sample points will automatically update their color based on this. However, constraints will become invalid and will have to be recalculated.
The 'Sampler' and 'SMT Solver' determine the tools used for these purposes. Currently, they are fixed to 'Rational function' and 'Z3'. Future versions may provide more alternatives.
