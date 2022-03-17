class Runner(object):
    def __init__(self, simulate_fun):
        self.simulate_fun = simulate_fun

    def run_function(self, inp):
        self.simulate_fun(inp)

    def run(self, inp):
        try:
            result = self.run_function(inp)
        except:
            result = None
        return result