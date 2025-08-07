from z3 import *
import sys

def main():
    data = sys.stdin.read().split()
    if not data:
        return
    
    n = int(data[0])
    deadline = int(data[1])
    start = list(map(int, data[2:2+n]))
    dur = list(map(int, data[2+n:2+2*n]))
    
    min_start = min(start)
    first_act_options = [j for j in range(n) if start[j] == min_start]
    if not first_act_options:
        print("No solution")
        return
    
    s = Solver()
    P = [Int(f'p_{i}') for i in range(n)]
    cs = [Int(f'cs_{i}') for i in range(n)]
    
    # Permutation constraints
    s.add(Distinct(P))
    for i in range(n):
        s.add(P[i] >= 0, P[i] < n)
    
    # First activity must have min_start
    s.add(Or([P[0] == j for j in first_act_options]))
    s.add(cs[0] == min_start)
    
    # Activity start time constraints
    for i in range(n):
        disj = []
        for j in range(n):
            disj.append(And(P[i] == j, cs[i] >= start[j]))
        s.add(Or(disj))
    
    # Chain constraints
    for i in range(1, n):
        dur_prev = Sum([If(P[i-1] == j, dur[j], 0) for j in range(n)])
        s.add(cs[i] == cs[i-1] + dur_prev)
    
    # Deadline constraint
    dur_last = Sum([If(P[n-1] == j, dur[j], 0) for j in range(n)])
    s.add(cs[n-1] + dur_last - 1 <= deadline)
    
    if s.check() == sat:
        m = s.model()
        P_val = [m.evaluate(P[i]).as_long() for i in range(n)]
        print(" ".join(map(str, P_val)))
    else:
        print("No solution")

if __name__ == "__main__":
    main()