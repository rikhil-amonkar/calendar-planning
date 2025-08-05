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
    
    start_arr = Array('start_arr', IntSort(), IntSort())
    end_arr = Array('end_arr', IntSort(), IntSort())
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    
    for i in range(n):
        start_arr = Store(start_arr, i, reqs[i][0])
        end_arr = Store(end_arr, i, reqs[i][1])
        dur_arr = Store(dur_arr, i, reqs[i][2])
    
    travel_arr = Array('travel_arr', IntSort(), IntSort())
    for i in range(n):
        for j in range(n):
            idx = i * n + j
            travel_arr = Store(travel_arr, idx, travel[i][j])
    
    order = [ Int('order_%d' % i) for i in range(n) ]
    S = [ Int('S_%d' % i) for i in range(n) ]
    
    opt = Optimize()
    opt.set("timeout", 300000)
    
    for i in range(n):
        opt.add(order[i] >= 0, order[i] < n)
    opt.add(Distinct(order))
    
    s0 = order[0]
    opt.add(S[0] >= Select(start_arr, s0))
    opt.add(S[0] + Select(dur_arr, s0) <= Select(end_arr, s0))
    
    for k in range(1, n):
        prev_req = order[k-1]
        curr_req = order[k]
        travel_idx = prev_req * n + curr_req
        travel_time = Select(travel_arr, travel_idx)
        prev_dur = Select(dur_arr, prev_req)
        curr_start = Select(start_arr, curr_req)
        curr_end = Select(end_arr, curr_req)
        curr_dur = Select(dur_arr, curr_req)
        
        opt.add(S[k] >= S[k-1] + prev_dur + travel_time)
        opt.add(S[k] >= curr_start)
        opt.add(S[k] + curr_dur <= curr_end)
    
    total_time = (S[n-1] + Select(dur_arr, order[n-1])) - S[0]
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