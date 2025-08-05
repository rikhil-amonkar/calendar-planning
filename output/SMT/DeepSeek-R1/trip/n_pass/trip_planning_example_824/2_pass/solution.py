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
    
    Order = IntVector('Order', n)
    solver = Solver()
    
    for i in range(n):
        solver.add(Order[i] >= 0)
        solver.add(Order[i] < m)
        
    for i in range(n-1):
        solver.add(Order[i] <= Order[i+1])
        
    for d in range(m):
        total_req = 0
        for i in range(n):
            total_req += If(Order[i] == d, reqs[i], 0)
        solver.add(total_req <= capacity)
    
    if solver.check() == sat:
        model = solver.model()
        out_lines = []
        for i in range(n):
            out_lines.append(str(model[Order[i]].as_long()))
        print("\n".join(out_lines))
    else:
        print("No solution")

if __name__ == "__main__":
    main()