from model import *

import z3
import conf

class Problem:
    def __init__(self, file):
        n = int(file.readline().strip())
        self.tasks = [
            Task.from_line(
                n, i, file.readline()) for i in range(
                1, n + 1)]
        self.task_map = dict()
        id = 1
        for t in self.tasks:
            t.add_deps(file.readline())
            self.task_map[t.id] = list(range(id, id + len(t.frags)))
            id += len(t.frags)

        # self._transitive_task_closure()

        self.frags = { f.id: f for f in sum(
                (t.generate_frags(
                    self.task_map) for t in self.tasks),
                list())}

        bitwidth = int(math.log(max(map(lambda f: len(f.start_range()), self.frags.values())),2)) + 2
        for frag in self.frags.values():
            frag.create_var(bitwidth)

        self.task_frag_map = dict()
        for t in self.tasks:
            self.task_frag_map[t.id] = [self.frags[id]
                                        for id in self.task_map[t.id]]

        self._transitive_dep_closure()

        self.begin_time = min(map(lambda x: x.start_time, self.tasks))
        self.end_time = max(map(lambda x: x.deadline, self.tasks))

        base = self.end_time - self.begin_time
        self.min_starts = len(self.frags) + 1 + base
        self.max_starts = len(self.frags) + 1 + \
            max(self.frags.keys()) * base + (base - 1)

        #self.solver = z3.Optimize()
        self.solver = z3.Optimize()

        if conf.BIT_VEC == True:
            self.n_tasks = z3.BitVec('n', int(math.log(len(self.tasks), 2)) + 1)
        else:
            self.n_tasks = z3.Int('n')

    def __repr__(self):
        return '\n'.join(repr(f) for f in self.frags.values())

    def _transitive_task_closure(self):
        # private method
        # finds the transitive closure of dependencies
        # ie: if T1 depends on T2 and T2 depends on T3, add a dependency from T1 to T3
        #
        deps = dict()

        def find_deps(t):
            if t in deps:
                return deps[t]
            ideps = sum(map(lambda x: find_deps(
                self.tasks[x - 1]), t.deps), t.deps)
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
            if i in deps:
                return deps[i]
            ideps = sum(map(lambda x: find_deps(
                x), self.frags[i].deps), self.frags[i].deps)
            deps[i] = ideps
            return deps[i]

        for i, f in self.frags.items():
            f.deps = find_deps(i)

    def time_range(self):
        return range(self.begin_time, self.end_time)

    def encode(self):
        # atomicity
        for task, frags in map(lambda x: (
                self.tasks[x[0] - 1], list(map(lambda y: self.frags[y], x[1]))), self.task_map.items()):
            self.solver.add(z3.Xor(z3.And(task.exec == 1, task.exec_bool == True), z3.And(task.exec == 0, task.exec_bool == False)))

        for i, frag in self.frags.items():
            # range
            if conf.BIT_VEC:
                self.solver.add(z3.ULT(frag.start(), frag.max_start()))
                self.solver.add(z3.ULE(frag.min_start(), frag.start()))
            else:
                self.solver.add(frag.start() < frag.max_start())
                self.solver.add(frag.min_start() <= frag.start())

            # dependencies
            for dep in map(lambda x: self.frags[x], frag.deps):
                self.solver.add(z3.Implies(frag.exec(), dep.exec()))
                if conf.BIT_VEC:
                    self.solver.add(
                        z3.Implies(
                            frag.exec(),
                            z3.UGE(frag.start(), dep.start() + dep.proc_time)))
                else:
                    self.solver.add(
                        z3.Implies(
                            frag.exec(),
                            frag.start() >= dep.start() + dep.proc_time))

            # exclusive access
            for j, frag2 in self.frags.items():
                if j == i: continue
                if conf.BIT_VEC:
                    self.solver.add(z3.Implies(z3.And(
                        frag.exec(), frag2.exec()),
                        z3.Xor(z3.UGE(frag.start(), frag2.start() + frag2.proc_time),
                               z3.UGE(frag2.start(), frag.start() + frag.proc_time))))
                else:
                    self.solver.add(z3.Implies(z3.And(
                        frag.exec(), frag2.exec()),
                        z3.Xor(frag.start() >= frag2.start() + frag2.proc_time,
                               frag2.start() >= frag.start() + frag.proc_time)))

        self.solver.add(self.n_tasks == z3.Sum([x.exec for x in self.tasks]))
        self.solver.maximize(self.n_tasks)

    def compute(self):
        assert self.solver.check() != z3.unsat, 'UNSAT'
        return self.solver.model()

    def solve(self):
        model = self.compute()
        print(model[self.n_tasks])
        for task, frags in self.task_frag_map.items():
            if int(str(model[self.tasks[task - 1].exec])) == 1:
                start_times = map(lambda f: f.min_start() +
                                  int(str(model[f.start_var])), frags)
                print(
                    '{} {}'.format(
                        task, ' '.join(
                            str(i) for i in start_times)))


if __name__ == '__main__':
    s = Problem(open('../tests/test1.sms'))
    s.encode()
    s.solve()
