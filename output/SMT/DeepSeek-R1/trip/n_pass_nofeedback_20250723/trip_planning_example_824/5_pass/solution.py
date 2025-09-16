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
    total_sum_val = sum(reqs)
    
    solver = Solver()
    
    solver.add(rt[0] == reqs[0])
    for i in range(1, n):
        solver.add(rt[i] == If(Break[i-1], reqs[i], rt[i-1] + reqs[i]))
    
    for i in range(n):
        solver.add(rt[i] >= 0)
        solver.add(rt[i] <= total_sum_val)
    
    for i in range(n-1):
        solver.add(Implies(Break[i], rt[i] <= capacity))
    solver.add(rt[n-1] <= capacity)
    
    total_breaks = Sum([If(Break[i], 1, 0) for i in range(n-1)])
    solver.add(total_breaks <= m-1)
    
    if solver.check() == sat:
        model = solver.model()
        days = [0] * n
        for i in range(1, n):
            if is_true(model.eval(Break[i-1])):
                days[i] = days[i-1] + 1
            else:
                days[i] = days[i-1]
        out_lines = [str(day) for day in days]
        print("\n".join(out_lines))
    else:
        print("No solution")

if __name__ == "__main__":
    main()