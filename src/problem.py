from model import *

import minizinc
import conf
import sys


class Problem:
    def __init__(self, file):
        self.solver = minizinc.Solver.lookup('gecode')
        self.n = int(file.readline().strip())

        self.model = minizinc.Model()
        self.model.add_string('array[1..{}] of var bool: exec;\n'.format(self.n+1))
        self.tasks = {i:
                      Task.from_line(self.model,
                          i, file.readline()) for i in range(
                          1, self.n + 1)}

        for t in self.tasks.values():
            t.add_deps(file.readline())

        cycle = self.find_task_cycle()
        while cycle is not None:
            self.remove_cycle(cycle)
            cycle = self.find_task_cycle()

        self.task_map = dict()

        id = 1
        for t in self.tasks.values():
            self.task_map[t.id] = list(range(id, id + len(t.frags)))
            id += len(t.frags)

        # self.transitive_task_closure()

        self.frags = {f.id: f for f in sum(
            (t.generate_frags(
                self.task_map) for t in self.tasks.values()),
            list())}

        self.task_frag_map = dict()
        for tid in self.tasks:
            self.task_frag_map[tid] = [self.frags[id]
                                       for id in self.task_map[tid]]
        self.transitive_dep_closure()


    def __repr__(self):
        return '\n'.join(repr(f) for f in self.frags.values())

    def transitive_task_closure(self):
        # private method
        # finds the transitive closure of dependencies
        # ie: if T1 depends on T2 and T2 depends on T3, add a dependency from T1 to T3
        #
        deps = dict()

        def find_deps(t):
            if t in deps:
                return deps[t]
            ideps = sum(map(lambda x: find_deps(
                self.tasks[x]), t.deps), t.deps)
            deps[t] = ideps
            return deps[t]

        for i, f in self.frags.items():
            find_deps(i)

        for i, f in self.frags.items():
            f.deps = find_deps(i)

    def transitive_dep_closure(self):
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
            find_deps(i)

        for i, f in self.frags.items():
            f.deps = find_deps(i)

    def remove_cycle(self, cycle):
        to_delete = [x for x in cycle]
        while len(to_delete) > 0:
            while len(to_delete) > 0:
                id = to_delete.pop()
                del(self.tasks[id])

            for t in self.tasks.values():
                if any(id not in self.tasks for id in t.deps):
                    to_delete.append(t.id)

    def find_task_cycle(self):
        stack = list()
        visited = set()

        def visit(self, task):
            if task.id in visited:
                return None
            if task.id in stack:
                return stack[stack.index(task.id):]
            stack.append(task.id)
            for tid in task.deps:
                task2 = self.tasks[tid]
                cycle = visit(self, task2)
                if cycle is not None:
                    return cycle
            stack.pop()
            visited.add(task.id)
            return None

        for t in self.tasks.values():
            cycle = visit(self, t)
            if cycle is not None:
                return cycle

        return None

    def encode(self):
        for i in range(self.n+1):
            if i not in self.tasks:
                self.model.add_string('constraint exec[{}] = false;\n'.format(i))

        for i, frag in self.frags.items():
            # dependencies
            for dep in map(lambda x: self.frags[x], frag.deps):
                self.model.add_string('constraint if {} then {} endif;\n'.format(frag.exec(), dep.exec()))
                self.model.add_string('constraint if {} then {} >= {} + {} endif;\n'.format(frag.exec(), frag.start(), dep.start(), dep.proc_time))


            # exclusive access
            for j, frag2 in self.frags.items():
                if j == i: # or frag2.deadline < frag.min_start() or frag.deadline < frag2.min_start():
                    continue

                #print(i, j, frag, frag2)
                #self.model.add_string('constraint {} != {};\n'.format(frag.start(), frag2.start()))
                self.model.add_string('constraint if {0} /\\ {1} then ({2} >= {3} + {5}) xor ({3} >= {2} + {4}) endif;\n'.format(
                    frag.exec(),
                    frag2.exec(),
                    frag.start(),
                    frag2.start(),
                    frag.proc_time,
                    frag2.proc_time))

        self.model.add_string('solve maximize sum(i in 0..{})(exec[i]);\n'.format(self.n+1))

    def compute(self):
        self.instance = minizinc.Instance(self.solver, self.model)
        #self.result = self.instance.solve(processes=96,optimization_level=5)
        self.result = self.instance.solve()
        assert self.result.status.has_solution(), 'UNSAT'
        return self.result

    def solve(self):
        result = self.compute()
       #print('---------------------')
       #print('\n'.join('{} {}'.format(t, ' '.join(str(f.min_start()) for f in frags)) for t, frags in self.task_frag_map.items()))
       #print('---------------------')
       #print(''.join(self.model._code_fragments))
       #print('---------------------')
        print(result['objective']-1)
        for task, frags in self.task_frag_map.items():
            if result['exec'][task]:
                start_times = map(lambda f: result[f.start_var], frags)
                print(
                    '{} {}'.format(
                        task, ' '.join(
                            str(i) for i in start_times)))


if __name__ == '__main__':
    s = Problem(open('../tests/test1.sms'))
    s.encode()
    s.solve()
