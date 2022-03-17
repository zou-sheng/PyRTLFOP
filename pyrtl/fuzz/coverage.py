from ..wire import *

class Coverage(object):
    def __init__(self, fuzzer):
        self.fuzzer = fuzzer
        self.all_coverage = set()
        self.cumulative_coverage = []

    def get_inputs(self):
        stimuli = {}
        for i in self.fuzzer.inputs:
            stimuli[i[0]] = self.fuzzer.sim.inspect(i[0])
        return stimuli

    def record(self):
        pass

    def coverage(self):
        return self.all_coverage

class StateCoverage(Coverage):
    def __init__(self, fuzzer):
        super().__init__(fuzzer)
        self.regs = {}
        for reg in self.fuzzer.block.wirevector_subset(Register):
            #print(reg.bitwidth)
            self.regs[reg.name] = [(self.get_inputs(), self.fuzzer.sim.inspect(reg.name), reg.bitwidth)]

    def record(self):
        for key in self.regs.keys():
            self.regs[key].append((self.get_inputs(), self.fuzzer.sim.inspect(key)))
            self.all_coverage.add((key, self.fuzzer.sim.inspect(key)))
        self.cumulative_coverage.append(len(self.all_coverage))

    def gen_state_transition(self):
        state_transition = {}
        for key in self.regs.keys():
            covered_state = list(map(lambda x: x[1], self.regs[key]))
            transitions = list(zip(covered_state, covered_state[1:]))
            state_transition[key] = transitions
        return state_transition

class MuxCoverage(Coverage):
    def __init__(self, fuzzer):
        super().__init__(fuzzer)
        self.muxes = {}
        for mux in self.fuzzer.block.logic_subset('x'):
            present_value = self.fuzzer.sim.inspect(mux.args[0].name)
            self.muxes[mux.args[0].name] = [(self.get_inputs(), present_value)]
        self.toggle_coverage = {}

    def record(self):
        for key in self.muxes.keys():
            if key=='tmp3':
                print(key, self.muxes[key][-1][1], self.fuzzer.sim.inspect(key))
            if self.muxes[key][-1][1] != self.fuzzer.sim.inspect(key):# and self.muxes[key][2] == False:
                present_value = self.fuzzer.sim.inspect(key)
                self.muxes[key].append((self.get_inputs(), present_value))
                self.all_coverage.add(key)
        #print(self.muxes)
        self.cumulative_coverage.append(len(self.all_coverage)/len(self.muxes))

    def toggle_coverage_statistic(self):
        covered = 0
        toggle_covered = set()
        total = len(self.muxes)
        for key in self.muxes.keys():
            if len(self.muxes[key]) > 2:
                self.toggle_coverage[key] = True
                covered += 1
                toggle_covered.add(key)
            else:
                self.toggle_coverage[key] = False
        return toggle_covered, covered / total

    def coverage(self):
        toggle_covered, percent = self.toggle_coverage_statistic()
        return set(toggle_covered)