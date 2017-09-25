"""Model repair finds parameter values that satisfy a PCTL property.

Given a parametric Markov chain and a PCTL property, model repair finds
parameter valuations for which the MC satisfies the property. (Such a
valuation is called a 'repair'.)

Optionally, a cost function over the parameters (e.g., distance from
some origin) can be specified. In this case the goal is to find a
'low-cost' repair, i.e., a repair for which the function is minimized.

If a cost threshold is specified, model repair terminates as soon as it
finds a repair that is at most this expensive. Otherwise, the procedure
continues until some internal termination criterion is met.

Exact solutions can be obtained by computing the rational function
representing the reachability probability / rewards of the parametric
model, but doing so can be computationally prohibitive.

For an approximate approach, model repair can be treated as a 'black
box' heuristic optimization problem. The objective (aka fitness)
function is then composed of the actual model checking result (in
particular penalizing any parameter valuation for which the property is
not satisfied) and the cost function. Particle swarm optimization is
one method that finds solutions relatively quickly but cannot guarantee
optimality (or even epsilon-approximate optimality).
"""
