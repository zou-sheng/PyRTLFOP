from .fuzzer import *
from .coverage import *
from .aflMutators import *

def add_test(all_coverage, coverage_and_test):
    # all_coverage is a dict with test as key and the corresponding coverage as value
    # coverage_and_test is a tuple with test and its corresponding coverage
    #1. Union all the coverage
    covered = set()
    newtest, newcoverage = coverage_and_test

    # if the coverage in coverage_and_test has not been covered, add it
    #print(covered, newcoverage, newcoverage - covered)
    for key in list(all_coverage):
        if all_coverage[key].issubset(newcoverage):
            all_coverage.pop(key)

    for key in all_coverage.keys():
        covered |= all_coverage[key]
    if len(newcoverage - covered) > 0:
        all_coverage[newtest] = newcoverage

    return all_coverage

def fuzzing(block, seeds, sorted_inputs=[], covtype='M', time=0, register_value_map=None, memory_value_map=None,
                 default_value=0,):
    """
    implemeting fuzzing algorithm:
    1. taking block and seeds as input, where block is commonly working_block
       and seeds is a string whose length equals numberOfInputs * cycles
    2. we first run DUT using seed selected from seeds. Here the seeds may be
       created randomly or by symbolic simulation. So we first run with it
    3. the coverage information are recored using the cov parameter.
    4. If coverage target is fulfilled, we stop fuzzing and return seeds
    5. Else, we then iterate over the seeds and apply various mutation algorithm
    6. after each mutation, we repeat simulation and coverage collection steps, until
       coverage target is obtained or time budget expired
    """
    # To Do
    all_coverage = {}
    for seed in seeds:
        covf = CoverageFuzzer(block, sorted_inputs, register_value_map, memory_value_map, default_value)
        if covtype == 'M':
            cov = MuxCoverage(covf)
        elif covtype == 'S':
            cov = StateCoverage(covf)
        covf.runs_with_coverage(seed, cov)
        coverage = cov.coverage()
        #print(coverage, all_coverage)
        add_test(all_coverage, (seed, coverage))
    mutations = []
    print('after first stage: ', all_coverage)
    for seed in seeds:
        for key in deterministic_mutators.keys():
            mutations += deterministic_mutate(seed, deterministic_mutators[key])
        for key in non_deterministic_mutators.keys():
            mutations += non_deterministic_mutate(seed, non_deterministic_mutators[key])
    print(len(mutations))#, mutations)
    for seed in mutations:
        covf = CoverageFuzzer(block, sorted_inputs, register_value_map, memory_value_map, default_value)
        if covtype == 'M':
            cov = MuxCoverage(covf)
        elif covtype == 'S':
            cov = StateCoverage(covf)
        covf.runs_with_coverage(seed, cov)
        coverage = cov.coverage()
        # print(key, coverage, all_coverage)
        add_test(all_coverage, (seed, coverage))

    return all_coverage


