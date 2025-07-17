from z3 import *

def main():
    # Define the travel time matrix (11x11)
    T = [
        [0, 6, 5, 8, 12, 21, 11, 21, 20, 10, 25],
        [8, 0, 11, 7, 9, 18, 12, 22, 17, 11, 27],
        [4, 10, 0, 11, 15, 21, 13, 19, 22, 8, 20],
        [8, 7, 11, 0, 7, 14, 7, 17, 14, 5, 21],
        [14, 10, 17, 8, 0, 11, 7, 16, 10, 12, 22],
        [19, 18, 22, 13, 9, 0, 10, 10, 7, 17, 16],
        [10, 13, 13, 7, 6, 12, 0, 11, 11, 8, 16],
        [20, 23, 21, 17, 17, 10, 12, 0, 15, 15, 6],
        [20, 19, 23, 14, 11, 7, 11, 15, 0, 18, 21],
        [9, 10, 9, 5, 11, 14, 8, 13, 17, 0, 17],
        [22, 24, 21, 18, 21, 16, 16, 6, 20, 16, 0]
    ]
    
    # Availability and min duration for friends (indices 1 to 10)
    available_start = [0] * 11
    available_end = [0] * 11
    min_duration = [0] * 11
    
    # Stephanie (node1): Fisherman's Wharf
    available_start[1] = 15*60 + 30   # 3:30PM
    available_end[1] = 22*60           # 10:00PM
    min_duration[1] = 30
    
    # Lisa (node2): Financial District
    available_start[2] = 10*60 + 45    # 10:45AM
    available_end[2] = 17*60 + 15      # 5:15PM
    min_duration[2] = 15
    
    # Melissa (node3): Russian Hill
    available_start[3] = 17*60         # 5:00PM
    available_end[3] = 21*60 + 45      # 9:45PM
    min_duration[3] = 120
    
    # Betty (node4): Marina District
    available_start[4] = 10*60 + 45    # 10:45AM
    available_end[4] = 14*60 + 15      # 2:15PM
    min_duration[4] = 60
    
    # Sarah (node5): Richmond District
    available_start[5] = 16*60 + 15    # 4:15PM
    available_end[5] = 19*60 + 30      # 7:30PM
    min_duration[5] = 105
    
    # Daniel (node6): Pacific Heights
    available_start[6] = 18*60 + 30    # 6:30PM
    available_end[6] = 21*60 + 45      # 9:45PM
    min_duration[6] = 60
    
    # Joshua (node7): Haight-Ashbury
    available_start[7] = 9*60          # 9:00AM
    available_end[7] = 15*60 + 30      # 3:30PM
    min_duration[7] = 15
    
    # Joseph (node8): Presidio
    available_start[8] = 9*60          # 9:00AM (adjusted from 7:00AM)
    available_end[8] = 13*60           # 1:00PM
    min_duration[8] = 45
    
    # Andrew (node9): Nob Hill
    available_start[9] = 19*60 + 45    # 7:45PM
    available_end[9] = 22*60           # 10:00PM
    min_duration[9] = 105
    
    # John (node10): The Castro
    available_start[10] = 13*60 + 15   # 1:15PM
    available_end[10] = 19*60 + 45     # 7:45PM
    min_duration[10] = 45
    
    # Create the solver
    opt = Optimize()
    
    # Define variables
    visited = [Bool(f'visited_{i}') for i in range(1, 11)]
    # For node0 (Embarcadero), we set visited_0 = True (but not a variable)
    
    # x[i][j] for i, j in 0..10, i != j
    x = [[Bool(f'x_{i}_{j}') for j in range(11)] for i in range(11)]
    
    # Time variables
    arrival_time = [Int(f'arrival_{i}') for i in range(11)]
    departure_time = [Int(f'departure_{i}') for i in range(11)]
    
    # Constraint: start at Embarcadero (node0) at 9:00AM (540 minutes)
    opt.add(arrival_time[0] == 540)
    opt.add(departure_time[0] == 540)
    
    # Constraint: no self loops
    for i in range(11):
        opt.add(Not(x[i][i]))
    
    # In_degree and out_degree for each node
    in_degree = [Sum([If(x[j][i], 1, 0) for j in range(11) if j != i]) for i in range(11)]
    out_degree = [Sum([If(x[i][j], 1, 0) for j in range(11) if j != i]) for i in range(11)]
    
    # Constraints for node0 (start)
    opt.add(out_degree[0] == 1)
    opt.add(in_degree[0] == 0)
    
    # For friends (nodes 1 to 10)
    k = Sum([If(visited_i, 1, 0) for visited_i in visited])
    for idx, i in enumerate(range(1, 11)):
        # visited_i corresponds to friend at node i
        visited_i = visited[idx]
        opt.add(in_degree[i] == If(visited_i, 1, 0))
        opt.add(out_degree[i] <= If(visited_i, 1, 0))
        opt.add(out_degree[i] >= 0)
    
    # Total out_degree from friends (nodes 1 to 10) should be k-1
    opt.add(Sum([out_degree[i] for i in range(1, 11)]) == k - 1)
    
    # Time constraints for friends
    for idx, i in enumerate(range(1, 11)):
        visited_i = visited[idx]
        # If visited, then constraints on times
        opt.add(If(visited_i,
                   And(
                       departure_time[i] >= arrival_time[i] + min_duration[i],
                       departure_time[i] >= available_start[i] + min_duration[i],
                       departure_time[i] <= available_end[i]
                   ),
                   True))
        
        # Also, if visited, arrival_time must be at least the departure from the previous node plus travel time
        for j in range(11):
            if j != i:
                opt.add(If(And(visited_i, x[j][i]),
                           arrival_time[i] >= departure_time[j] + T[j][i],
                           True))
    
    # Objective: maximize the number of friends visited (k)
    opt.maximize(k)
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        total_visited = m.evaluate(k).as_long()
        print(f"Total friends met: {total_visited}")
        
        # Print the path and schedule
        path = []
        current = 0  # Start at Embarcadero
        path.append(0)
        next_node = None
        for j in range(11):
            if j != current and m.evaluate(x[current][j]):
                next_node = j
                break
        while next_node is not None:
            path.append(next_node)
            current = next_node
            next_node = None
            for j in range(11):
                if j != current and m.evaluate(x[current][j]):
                    next_node = j
                    break
        
        # Print the path
        location_names = [
            "Embarcadero",
            "Fisherman's Wharf (Stephanie)",
            "Financial District (Lisa)",
            "Russian Hill (Melissa)",
            "Marina District (Betty)",
            "Richmond District (Sarah)",
            "Pacific Heights (Daniel)",
            "Haight-Ashbury (Joshua)",
            "Presidio (Joseph)",
            "Nob Hill (Andrew)",
            "The Castro (John)"
        ]
        print("Schedule:")
        for node in path:
            if node == 0:
                print(f"  Start at {location_names[0]} at 9:00 AM (540 minutes)")
            else:
                idx = node - 1
                if m.evaluate(visited[idx]):
                    arr = m.evaluate(arrival_time[node]).as_long()
                    dep = m.evaluate(departure_time[node]).as_long()
                    start_meeting = max(arr, available_start[node])
                    # Convert minutes to time string
                    start_hour = start_meeting // 60
                    start_min = start_meeting % 60
                    end_hour = dep // 60
                    end_min = dep % 60
                    print(f"  Meet at {location_names[node]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d} (Duration: {dep - start_meeting} minutes)")
                else:
                    print(f"  Not meeting at {location_names[node]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()