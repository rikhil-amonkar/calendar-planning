import sys
from z3 import *

def main():
    data = sys.stdin.read().split()
    if not data:
        return
    
    n = int(data[0])
    m = int(data[1])
    capacity = int(data[2])
    reqs = list(map(int, data[3:3+n]))
    
    Break = [Bool(f'Break_{i}') for i in range(n-1)]
    rt = [Int(f'rt_{i}') for i in range(n)]
    Day = [Int(f'Day_{i}') for i in range(n)]
    
    solver = Solver()
    
    solver.add(rt[0] == reqs[0])
    solver.add(Day[0] == 0)
    
    for i in range(1, n):
        solver.add(rt[i] == If(Break[i-1], reqs[i], rt[i-1] + reqs[i]))
        solver.add(Day[i] == Day[i-1] + If(Break[i-1], 1, 0))
    
    for i in range(n-1):
        solver.add(If(Break[i], rt[i] <= capacity, True))
    solver.add(rt[n-1] <= capacity)
    
    solver.add(Day[n-1] < m)
    
    if solver.check() == sat:
        model = solver.model()
        out_lines = []
        for i in range(n):
            out_lines.append(str(model[Day[i]].as_long()))
        print("\n".join(out_lines))
    else:
        print("No solution")

if __name__ == "__main__":
    main()