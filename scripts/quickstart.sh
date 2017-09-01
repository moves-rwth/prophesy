# 1. Computing rational function
echo "##########"
echo "1. Computing rational function"
echo "##########\n"
./scripts/compute_solutionfunction.py --file benchmarkfiles/nand/nand.pm --const "N=2,K=1" --pctl-file benchmarkfiles/nand/property1.pctl --result-file benchmarkfiles/nand/nand_2-1.rat --storm
# Result is written to benchmarkfiles/nand/nand_2-1.rat


# 2. Sampling
# Here we have two options:
# a) Solution function (needs rational function)
# b) Model (needs no rational function)

# For a) (Solution function)
echo "\n##########"
echo "2a) Sampling using the solution function"
echo "##########\n"
./scripts/sampling_solutionfunction.py --rat-file benchmarkfiles/nand/nand_2-1.rat --samples-file benchmarkfiles/nand/nand_2-1.samples --samplingnr 5 --iterations 3 --threshold 0.35

# For b) (Model)
echo "\n##########"
echo "2b) Sampling using the model"
echo "##########\n"
 ./scripts/sampling_model.py --file benchmarkfiles/nand/nand.pm --const "N=2,K=1" --pctl-file benchmarkfiles/nand/property1.pctl --samplingnr 5 --iterations 3 --threshold 0.35 --storm

# All sample points are written to benchmarkfiles/nand/nand_2-1.samples


# 3. Parameter space partitioning
# Here we have three options:
# a) Solution function and SMT (needs rational function and SMT solver)
# b) Parameter lifting PLA (needs no rational function and no SMT solver)
# c) Direct encoding and SMT (needs no rational function but an SMT solver)

# For a) (Solution function)
echo "\n##########"
echo "3a) Parameter space partitioning using the solution function"
echo "##########\n"
./scripts/parameter_space_partitioning.py --rat-file benchmarkfiles/nand/nand_2-1.rat --samples-file benchmarkfiles/nand/nand_2-1.samples --storm --sfsmt --z3 --threshold "0.35" --quads --area 0.30 --plot-candidates --plot-every-n 1

# For b) (PLA)
echo "\n##########"
echo "3b) Parameter space partitioning using PLA"
echo "##########\n"
./scripts/parameter_space_partitioning.py --model-file benchmarkfiles/nand/nand.pm --const "N=2,K=1" --property-file benchmarkfiles/nand/property1.pctl --samples-file benchmarkfiles/nand/nand_2-1.samples --storm --pla --threshold "0.35" --rectangles --area 0.30 --epsilon-pmc 0.001 --plot-candidates --plot-every-n 1

# For c) (Direct SMT encoding)
echo "\n##########"
echo "3c) Parameter space partitioning using direct SMT encoding"
echo "##########\n"
./scripts/parameter_space_partitioning.py --model-file benchmarkfiles/nand/nand.pm --const "N=2,K=1" --property-file benchmarkfiles/nand/property1.pctl --samples-file benchmarkfiles/nand/nand_2-1.samples --storm --etr --z3 --threshold "0.35" --quads --area 0.30 --plot-candidates --plot-every-n 1

# All three options generate a PDF visualizing the parameter regions (if —-plot-candidates is given)
# Instead of uniform splitting via —-quads one can also use growing rectangles via --rectangles
