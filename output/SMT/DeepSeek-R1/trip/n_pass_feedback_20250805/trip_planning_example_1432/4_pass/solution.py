from z3 import *
import sys

def main():
    data = sys.stdin.readline().split()
    if not data:
        return
    
    try:
        n = int(data[0])
        deadline = int(data[1])
    except (IndexError, ValueError):
        print("No solution")
        return
        
    if len(data) < 2 + 2*n:
        print("No solution")
        return
        
    start = list(map(int, data[2:2+n]))
    dur = list(map(int, data[2+n:2+2*n]))
    
    min_start = min(start)
    first_act_options = [j for j in range(n) if start[j] == min_start]
    if not first_act_options:
        print("No solution")
        return
    
    s = Solver()
    P = [Int('p_%i' % i) for i in range(n)]
    cs = [Int('cs_%i' % i) for i in range(n)]
    
    start_arr = Array('start_arr', IntSort(), IntSort())
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    
    for j in range(n):
        s.add(start_arr[j] == start[j])
        s.add(dur_arr[j] == dur[j])
    
    s.add(Distinct(P))
    for i in range(n):
        s.add(P[i] >= 0)
        s.add(P[i] < n)
        
    s.add(Or([P[0] == j for j in first_act_options]))
    s.add(cs[0] == min_start)
    
    for i in range(n):
        s.add(cs[i] >= start_arr[P[i]])
    
    for i in range(1, n):
        s.add(cs[i] == cs[i-1] + dur_arr[P[i-1]])
    
    s.add(cs[n-1] + dur_arr[P[n-1]] <= deadline + 1)
    
    if s.check() == sat:
        m = s.model()
        P_val = [m.evaluate(P[i]) for i in range(n)]
        P_val = [p_val.as_long() for p_val in P_val]
        print(" ".join(map(str, P_val)))
    else:
        print("No solution")

if __name__ == "__main__":
    main()