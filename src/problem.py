from model import *

import z3

class Problem:
    def __init__(self, file):
        n = int(file.readline().strip())
        self.tasks = [Task.from_line(i, file.readline()) for i in range(1, n+1)]
        self.task_map = dict()
        id = 1
        for t in self.tasks:
            t.add_deps(file.readline())
            self.task_map[t.id] = list(range(id, id + len(t.frags)))
            id += len(t.frags)

        self._transitive_task_closure()

        self.frags = {
            f.id: f for f in sum(
                (t.generate_frags(
                    self.task_map) for t in self.tasks),
                list())}

        self.begin_time = min(map(lambda x: x.start_time, self.tasks))
        self.end_time = max(map(lambda x: x.deadline, self.tasks))

        base = self.end_time - self.begin_time
        self.min_starts = len(self.frags) + 1 + base
        self.max_starts = len(self.frags) + 1 + max(self.frags.keys()) * base + (base - 1)

        self.solver = z3.Solver()

    def __repr__(self):
        return '\n'.join(repr(f) for f in self.frags.values())

    def _transitive_task_closure(self):
        # private method
        # finds the transitive closure of dependencies
        # ie: if T1 depends on T2 and T2 depends on T3, add a dependency from T1 to T3
        #
        deps = dict()
        def find_deps(t):
            if t in deps: return deps[t]
            ideps = sum(map(lambda x: find_deps(self.tasks[x - 1]), t.deps), t.deps)
            deps[t] = ideps
            return deps[t]

        for t in self.tasks:
            t.deps = find_deps(t)

    def _transitive_dep_closure(self):
        # private method
        # finds the transitive closure of dependencies
        # ie: if F1 depends on F2 and F2 depends on F3, add a dependency from F1 to F3
        #
        deps = dict()
        def find_deps(i):
            if i in deps: return deps[i]
            ideps = sum(map(lambda x: find_deps(x), self.frags[i].deps), self.frags[i].deps)
            deps[i] = ideps
            return deps[i]

        for i, f in self.frags.items():
            f.deps = find_deps(i)

    def time_range(self):
        return range(self.begin_time, self.end_time)

    def encode(self):
        # atomicity
        #for task in map(lambda x: list(map(lambda y: self.frags[y], x)), self.task_map.values()):
            #self.solver.add(z3.Or(z3.And([frag.start > self.end_time for frag in task]), z3.And([z3.And(self.begin_time <= frag.start, frag.start <= self.end_time) for frag in task])))

        for i, frag in self.frags.items():
            # fragment needs to start in an interval
            #self.solver.add(z3.Or(z3.And(frag.min_start() <= frag.start, frag.start < frag.max_start()), frag.start > self.end_time))
            self.solver.add(z3.And(frag.min_start() <= frag.start, frag.start < frag.max_start()))

            # dependencies
            for dep in map(lambda x: self.frags[x], frag.deps):
                self.solver.add(dep.start < frag.start)

            # exclusive access
            for j, frag2 in self.frags.items():
                if j == i: continue
                self.solver.add(z3.Or(frag.start >= frag2.start + frag2.proc_time, frag2.start >= frag.start + frag.proc_time))

    def compute(self):
        assert self.solver.check() != z3.unsat, 'UNSAT'
        return self.solver.model()

    def solve(self):
        model = self.compute()
        print(len(self.tasks))
        for task, frags in self.task_map.items():
            start_times = list(map(lambda f: model[self.frags[f].start], frags))
            if len(start_times) > 0:
                print('{} {}'.format(task, ' '.join(str(i) for i in start_times)))

if __name__ == '__main__':
    s = Problem(open('../tests/test1.sms'))
    s.encode()
    s.solve()
