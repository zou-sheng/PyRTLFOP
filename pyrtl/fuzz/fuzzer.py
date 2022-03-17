#import random
from ..wire import *
from ..simulation import Simulation
from ..simulation import SimulationTrace

class CoverageFuzzer(object):
    def __init__(self, block, sorted_inputs, register_value_map=None, memory_value_map=None,
                 default_value=0, simTrace=True):
        self.block = block
        self.sorted_inputs = sorted_inputs
        self.inputs = []
        self.inputs_bitwidth = 0
        if len(sorted_inputs) <= 0:
            sorted_inps = block.wirevector_subset(Input)
        else:
            sorted_inps = [i for si in sorted_inputs for i in block.wirevector_subset(Input) if si == i.name]
        for i in sorted_inps:
            self.inputs.append((i.name, i.bitwidth))
            self.inputs_bitwidth += i.bitwidth
        #print(self.inputs)
        if simTrace:
            sim_trace = SimulationTrace()
        else:
            sim_trace = None
        self.sim_trace = sim_trace
        self.register_value_map = register_value_map
        self.memory_value_map = memory_value_map
        self.default_value = default_value
        self.sim = Simulation(self.sim_trace, register_value_map, memory_value_map, default_value)
        self.runner = self.sim.step
        self.cycle = 0

    def fuzz(self, inp):
        one_cycle_length = self.inputs_bitwidth
        assert self.cycle <= len(inp) // one_cycle_length
        #print(self.cycle)
        stimuli = {}
        current_cycle_stimuli = inp[self.cycle * one_cycle_length:(self.cycle + 1) * one_cycle_length]
        #print(current_cycle_stimuli)
        self.cycle += 1
        index = 0
        for inp in self.inputs:
            stimuli[inp[0]] = int(current_cycle_stimuli[index:index + inp[1]], 2)
            index += inp[1]
        #print(stimuli)
        return stimuli

    def run(self, inp):
        #print('1')
        self.runner(self.fuzz(inp))

    def runs(self, inp):
        for i in range(len(inp) // self.inputs_bitwidth):
            self.run(inp)

    def runs_with_coverage(self, inp, cov):
        #print('2')
        #print(len(inp) // self.inputs_bitwidth)
        for i in range(len(inp) // self.inputs_bitwidth):
            self.run(inp)
            cov.record()

    #def concate_inputs(self):
    #    s = ''
    #    for i in self.inputs:
    #       s += int2bin(self.sim.inspect(i[0]), i[1])
    #    return s


