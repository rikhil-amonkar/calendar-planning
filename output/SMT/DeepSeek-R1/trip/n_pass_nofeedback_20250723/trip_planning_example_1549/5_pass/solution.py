from z3 import *

def main():
    import sys
    data = sys.stdin.read().split()
    if not data:
        return
    
    n = int(data[0])
    reqs = []
    index = 1
    for i in range(n):
        s = int(data[index])
        e = int(data[index+1])
        d = int(data[index+2])
        index += 3
        reqs.append((s, e, d))
        
    travel = []
    for i in range(n):
        row = []
        for j in range(n):
            row.append(int(data[index]))
            index += 1
        travel.append(row)
    
    order = [Int(f'order_{i}') for i in range(n)]
    S = [Int(f'S_{i}') for i in range(n)]
    s = Solver()
    
    # Domain constraints for order variables
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Helper functions using If expressions
    def get_start(req_idx):
        expr = reqs[0][0]
        for i in range(1, n):
            expr = If(req_idx == i, reqs[i][0], expr)
        return expr

    def get_end(req_idx):
        expr = reqs[0][1]
        for i in range(1, n):
            expr = If(req_idx == i, reqs[i][1], expr)
        return expr

    def get_dur(req_idx):
        expr = reqs[0][2]
        for i in range(1, n):
            expr = If(req_idx == i, reqs[i][2], expr)
        return expr

    def get_travel(from_idx, to_idx):
        expr = travel[0][0]
        for i in range(n):
            for j in range(n):
                expr = If(And(from_idx == i, to_idx == j), travel[i][j], expr)
        return expr

    # Time window constraints for the first request
    s.add(S[0] >= get_start(order[0]))
    s.add(S[0] + get_dur(order[0]) <= get_end(order[0]))
    
    # Constraints for subsequent requests
    for k in range(1, n):
        prev_req = order[k-1]
        curr_req = order[k]
        travel_time = get_travel(prev_req, curr_req)
        prev_dur = get_dur(prev_req)
        curr_start = get_start(curr_req)
        curr_dur = get_dur(curr_req)
        curr_end = get_end(curr_req)
        
        s.add(S[k] >= S[k-1] + prev_dur + travel_time)
        s.add(S[k] >= curr_start)
        s.add(S[k] + curr_dur <= curr_end)
    
    # Minimize total time
    total_time = (S[n-1] + get_dur(order[n-1])) - S[0]
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(total_time)
    
    if opt.check() == sat:
        m = opt.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_vals = [m.evaluate(S[i]).as_long() for i in range(n)]
        
        # Map start times to original request indices
        start_times = [0] * n
        for i in range(n):
            req_index = order_vals[i]
            start_times[req_index] = start_vals[i]
        
        print(" ".join(map(str, order_vals)))
        print(" ".join(map(str, start_times)))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()