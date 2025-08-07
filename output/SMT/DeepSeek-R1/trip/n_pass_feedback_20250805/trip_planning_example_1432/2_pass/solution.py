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
        
    s.add(cs[0] == min_start)
    
    for i in range(n):
        s.add(cs[i] >= start_arr[P[i]])
    
    for i in range(1, n):
        s.add(cs[i] == cs[i-1] + dur_arr[P[i-1]])
    
    s.add(cs[n-1] + dur_arr[P[n-1]] - 1 <= deadline)
    
    if s.check() == sat:
        m = s.model()
        P_val = [m.evaluate(P[i]) for i in range(n)]
        P_val = [p_val.as_long() for p_val in P_val]
        print(" ".join(map(str, P_val)))
    else:
        print("No solution")

if __name__ == "__main__":
    main()