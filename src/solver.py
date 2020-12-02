#!/usr/bin/env python3

import sys
from problem import Problem
import time

if __name__ == '__main__':
    p = Problem(sys.stdin)
    begin = time.process_time()
    p.encode()
    p.solve()
    # print('{} s'.format(time.process_time() - begin), file=sys.stderr)
