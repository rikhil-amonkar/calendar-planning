from z3 import *

def main():
    import sys
    data = sys.stdin.read().split()
    if not data:
        return
    
    n = int(data[0]); m = int(data[1])
    start_node = int(data[2]); end_node = int(data[3])
    n_pass = int(data[4])
    passes = []
    index = 5
    for i in range(n_pass):
        node = int(data[index]); seq = int(data[index+1]); index += 2
        passes.append((node, seq))
    
    # Sort passes by sequence number
    passes.sort(key=lambda x: x[1])
    pass_nodes = [node for node, seq in passes]  # nodes in collection order
    
    # Build graph: matrix of travel times
    graph = [[1000000] * n for _ in range(n)]
    for i in range(m):
        u = int(data[index]); v = int(data[index+1]); t = int(data[index+2]); index += 3
        graph[u][v] = t
    
    max_time = 200  # increased max time steps
    
    # State variables
    locations = [Int('loc_%d' % i) for i in range(max_time+1)]
    times = [Int('time_%d' % i) for i in range(max_time+1)]
    pass_times = [Int('pass_%d_time' % i) for i in range(n_pass)]  # time indices
    
    s = Solver()
    
    # Initial and final conditions
    s.add(locations[0] == start_node)
    s.add(times[0] == 0)
    s.add(locations[max_time] == end_node)
    
    # Pass collection constraints
    for i in range(n_pass):
        s.add(pass_times[i] >= 0, pass_times[i] <= max_time)
        s.add(locations[pass_times[i]] == pass_nodes[i])  # simplified constraint
        
    # Pass collection order
    for i in range(1, n_pass):
        s.add(pass_times[i] > pass_times[i-1])
    
    # First-visit constraints for passes
    for i in range(n_pass):
        if i == 0:
            # Before first pass collection
            for t in range(0, max_time):
                s.add(Implies(t < pass_times[i], locations[t] != pass_nodes[i]))
        else:
            # Between previous pass and current pass
            for t in range(0, max_time):
                s.add(Implies(And(t > pass_times[i-1], t < pass_times[i]), 
                              locations[t] != pass_nodes[i]))
    
    # Movement constraints
    for t in range(max_time):
        options = []
        # Staying in place
        options.append(And(locations[t] == locations[t+1], times[t] == times[t+1]))
        # Moving to adjacent node
        for u in range(n):
            for v in range(n):
                if u != v and graph[u][v] != 1000000:
                    options.append(And(
                        locations[t] == u,
                        locations[t+1] == v,
                        times[t+1] == times[t] + graph[u][v]
                    ))
        s.add(Or(options))
    
    # Time must be non-decreasing
    for t in range(max_time):
        s.add(times[t+1] >= times[t])
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        total_time = m.eval(times[max_time])
        actual_pass_times = [m.eval(times[pt]) for pt in pass_times]
        print(total_time)
        for t in actual_pass_times:
            print(t)
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()