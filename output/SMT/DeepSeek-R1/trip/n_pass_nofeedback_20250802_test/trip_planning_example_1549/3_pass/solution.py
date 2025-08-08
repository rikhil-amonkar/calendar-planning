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
    
    order = [ Int('order_%d' % i) for i in range(n) ]
    S = [ Int('S_%d' % i) for i in range(n) ]
    
    opt = Optimize()
    opt.set("timeout", 300000)
    
    for i in range(n):
        opt.add(order[i] >= 0, order[i] < n)
    opt.add(Distinct(order))
    
    def get_start(req_idx):
        expr = IntVal(reqs[0][0])
        for i in range(1, n):
            expr = If(req_idx == i, IntVal(reqs[i][0]), expr)
        return expr

    def get_end(req_idx):
        expr = IntVal(reqs[0][1])
        for i in range(1, n):
            expr = If(req_idx == i, IntVal(reqs[i][1]), expr)
        return expr

    def get_dur(req_idx):
        expr = IntVal(reqs[0][2])
        for i in range(1, n):
            expr = If(req_idx == i, IntVal(reqs[i][2]), expr)
        return expr

    travel_z3 = [[IntVal(travel[i][j]) for j in range(n)] for i in range(n)]
    def get_travel(req1, req2):
        expr = travel_z3[0][0]
        for i in range(n):
            for j in range(n):
                expr = If(And(req1 == i, req2 == j), travel_z3[i][j], expr)
        return expr

    start0 = get_start(order[0])
    end0 = get_end(order[0])
    dur0 = get_dur(order[0])
    opt.add(S[0] >= start0)
    opt.add(S[0] + dur0 <= end0)
    
    for k in range(1, n):
        prev_req = order[k-1]
        curr_req = order[k]
        travel_time = get_travel(prev_req, curr_req)
        prev_dur = get_dur(prev_req)
        curr_start = get_start(curr_req)
        curr_end = get_end(curr_req)
        curr_dur = get_dur(curr_req)
        
        opt.add(S[k] >= S[k-1] + prev_dur + travel_time)
        opt.add(S[k] >= curr_start)
        opt.add(S[k] + curr_dur <= curr_end)
    
    total_time = (S[n-1] + get_dur(order[n-1])) - S[0]
    opt.minimize(total_time)
    
    if opt.check() == sat:
        m = opt.model()
        order_list = []
        for i in range(n):
            order_val = m.evaluate(order[i])
            order_list.append(order_val.as_long())
        
        start_times_in_order = [m.evaluate(S[i]) for i in range(n)]
        start_times = [0] * n
        for i in range(n):
            req_index = order_list[i]
            start_val = start_times_in_order[i]
            start_times[req_index] = start_val.as_long()
        
        print(" ".join(map(str, order_list)))
        print(" ".join(map(str, start_times)))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()