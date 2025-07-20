from z3 import *

def main():
    # Travel times: 9x9 matrix (0: Union Square, 1: Russian Hill, 2: Alamo Square, 3: Haight-Ashbury, 4: Marina District, 5: Bayview, 6: Chinatown, 7: Presidio, 8: Sunset District)
    travel_time = [
        [0, 13, 15, 18, 18, 15, 7, 24, 27],
        [10, 0, 15, 17, 7, 23, 9, 14, 23],
        [14, 13, 0, 5, 15, 16, 15, 17, 16],
        [19, 17, 5, 0, 17, 18, 19, 15, 15],
        [16, 8, 15, 16, 0, 27, 15, 10, 19],
        [18, 23, 16, 19, 27, 0, 19, 32, 23],
        [7, 7, 17, 19, 12, 20, 0, 19, 29],
        [22, 14, 19, 15, 11, 31, 21, 0, 15],
        [30, 24, 17, 15, 21, 22, 30, 16, 0]
    ]
    
    # Friend data: node index, available_start (minutes after 9AM), available_end, min_duration
    # For node0 (Union Square): not used for meeting
    available_start = [0] * 9
    available_end = [0] * 9
    min_duration = [0] * 9
    
    # Betty: Russian Hill (node1)
    available_start[1] = 0
    available_end[1] = 465
    min_duration[1] = 105
    
    # Melissa: Alamo Square (node2)
    available_start[2] = 30
    available_end[2] = 495
    min_duration[2] = 105
    
    # Joshua: Haight-Ashbury (node3)
    available_start[3] = 195
    available_end[3] = 600
    min_duration[3] = 90
    
    # Jeffrey: Marina District (node4)
    available_start[4] = 195
    available_end[4] = 540
    min_duration[4] = 45
    
    # James: Bayview (node5)
    available_start[5] = 0
    available_end[5] = 660
    min_duration[5] = 90
    
    # Anthony: Chinatown (node6)
    available_start[6] = 165
    available_end[6] = 270
    min_duration[6] = 75
    
    # Timothy: Presidio (node7)
    available_start[7] = 210
    available_end[7] = 345
    min_duration[7] = 90
    
    # Emily: Sunset District (node8)
    available_start[8] = 630
    available_end[8] = 750
    min_duration[8] = 120
    
    s = Solver()
    
    # Meet variables for friends (nodes 1 to 8)
    meet = [Bool(f"meet_{i}") for i in range(1, 9)]
    
    # x[i][j]: from node i to node j (j from 1 to 8). i in [0,8], j in [1,8]
    x = []
    for i in range(0, 9):
        x_i = []
        for j in range(1, 9):
            if i != j:
                x_i.append(Bool(f"x_{i}_{j}"))
            else:
                x_i.append(None)
        x.append(x_i)
    
    # u: position in the path for nodes 0 to 8
    u = [Int(f"u_{i}") for i in range(0, 9)]
    
    # Time variables for nodes 0 to 8
    arrival_time = [Int(f"arrival_{i}") for i in range(0, 9)]
    departure_time = [Int(f"departure_{i}") for i in range(0, 9)]
    
    # Constraints for start node (0)
    s.add(u[0] == 0)
    s.add(arrival_time[0] == 0)
    s.add(departure_time[0] == 0)
    
    # Bounds for time variables
    for i in range(0, 9):
        s.add(arrival_time[i] >= 0)
        s.add(arrival_time[i] <= 750)
        s.add(departure_time[i] >= 0)
        s.add(departure_time[i] <= 750)
        s.add(u[i] >= 0)
        s.add(u[i] <= 8)
    
    # Constraints for friends (nodes 1 to 8)
    for j in range(1, 9):
        j_index_in_meet = j - 1
        
        # meet[j-1] is true iff there is an incoming edge to j
        incoming_edges = []
        for i in range(0, 9):
            if i != j and x[i][j_index_in_meet] is not None:
                incoming_edges.append(x[i][j_index_in_meet])
        s.add(meet[j_index_in_meet] == Or(incoming_edges))
        
        # If meeting j, then exactly one incoming edge
        s.add(If(meet[j_index_in_meet], Sum([If(x[i][j_index_in_meet], 1, 0) for i in range(0,9) if i != j and x[i][j_index_in_meet] is not None]) == 1, True))
        
        # If not meeting j, then no incoming edge
        s.add(If(Not(meet[j_index_in_meet]), Sum([If(x[i][j_index_in_meet], 1, 0) for i in range(0,9) if i != j and x[i][j_index_in_meet] is not None]) == 0, True))
        
        # MTZ: for each possible incoming edge, if taken then u[j] = u[i] + 1
        for i in range(0, 9):
            if i != j and x[i][j_index_in_meet] is not None:
                s.add(Implies(x[i][j_index_in_meet], u[j] == u[i] + 1))
        
        # Arrival time at j: if there is an incoming edge from i, then arrival_time[j] = departure_time[i] + travel_time[i][j]
        for i in range(0, 9):
            if i != j and x[i][j_index_in_meet] is not None:
                s.add(Implies(x[i][j_index_in_meet], arrival_time[j] == departure_time[i] + travel_time[i][j]))
        
        # Meeting constraints: only if meet[j] is true
        # Start time is max(arrival_time[j], available_start[j])
        start_time_j = If(arrival_time[j] >= available_start[j], arrival_time[j], available_start[j])
        # Departure time = start_time_j + min_duration[j]
        s.add(Implies(meet[j_index_in_meet], departure_time[j] == start_time_j + min_duration[j]))
        s.add(Implies(meet[j_index_in_meet], departure_time[j] <= available_end[j]))
        s.add(Implies(meet[j_index_in_meet], arrival_time[j] <= available_end[j] - min_duration[j]))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(meet_i, 1, 0) for meet_i in meet])
    s.maximize(objective)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        num_met = m.evaluate(objective)
        print(f"Number of friends met: {num_met}")
        
        # Print schedule
        print("\nSchedule:")
        # Get the order of visited nodes
        positions = {}
        for j in range(0, 9):
            u_val = m.evaluate(u[j])
            if is_int_value(u_val):
                positions[j] = u_val.as_long()
        
        # Sort by position
        sorted_nodes = sorted(positions.keys(), key=lambda k: positions[k])
        # Only include nodes that are met (for j>=1) or the start (j=0)
        schedule_nodes = []
        for node in sorted_nodes:
            if node == 0:
                schedule_nodes.append(node)
            else:
                if m.evaluate(meet[node-1]):
                    schedule_nodes.append(node)
        
        # Print the path
        prev_time = 0
        prev_node = -1
        for node in schedule_nodes:
            if node == 0:
                print(f"Start at Union Square at 9:00 AM (0 minutes).")
                prev_node = 0
                continue
            
            # Travel from previous node to this node
            travel_time_val = travel_time[prev_node][node]
            arr_time_val = m.evaluate(arrival_time[node])
            if is_int_value(arr_time_val):
                arr_minutes = arr_time_val.as_long()
                hours, minutes = divmod(arr_minutes, 60)
                start_hour = 9 + hours
                start_min = minutes
                am_pm = "AM" if start_hour < 12 else "PM"
                if start_hour > 12:
                    start_hour -= 12
                start_time_str = f"{start_hour}:{minutes:02d} {am_pm}"
            else:
                start_time_str = "???"
            
            # Friend name
            friend_names = {
                1: "Betty (Russian Hill)",
                2: "Melissa (Alamo Square)",
                3: "Joshua (Haight-Ashbury)",
                4: "Jeffrey (Marina District)",
                5: "James (Bayview)",
                6: "Anthony (Chinatown)",
                7: "Timothy (Presidio)",
                8: "Emily (Sunset District)"
            }
            friend_name = friend_names[node]
            
            # Meeting start and end times
            dep_time_val = m.evaluate(departure_time[node])
            if is_int_value(dep_time_val):
                dep_minutes = dep_time_val.as_long()
                hours, minutes = divmod(dep_minutes, 60)
                end_hour = 9 + hours
                end_min = minutes
                am_pm = "AM" if end_hour < 12 else "PM"
                if end_hour > 12:
                    end_hour -= 12
                end_time_str = f"{end_hour}:{minutes:02d} {am_pm}"
            else:
                end_time_str = "???"
            
            print(f"Travel from {prev_node} to {node} took {travel_time_val} minutes.")
            print(f"Meet {friend_name} from {start_time_str} to {end_time_str}.")
            prev_node = node
            prev_time = dep_time_val
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()