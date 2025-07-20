from z3 import *

def main():
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
    
    available_start = [0] * 9
    available_end = [0] * 9
    min_duration = [0] * 9
    
    available_start[1] = 0
    available_end[1] = 465
    min_duration[1] = 105
    
    available_start[2] = 30
    available_end[2] = 495
    min_duration[2] = 105
    
    available_start[3] = 195
    available_end[3] = 600
    min_duration[3] = 90
    
    available_start[4] = 195
    available_end[4] = 540
    min_duration[4] = 45
    
    available_start[5] = 0
    available_end[5] = 660
    min_duration[5] = 90
    
    available_start[6] = 165
    available_end[6] = 270
    min_duration[6] = 75
    
    available_start[7] = 210
    available_end[7] = 345
    min_duration[7] = 90
    
    available_start[8] = 630
    available_end[8] = 750
    min_duration[8] = 120
    
    opt = Optimize()
    
    meet = [Bool(f"meet_{i}") for i in range(1, 9)]
    
    x = []
    for i in range(0, 9):
        x_i = []
        for j in range(1, 9):
            if i != j:
                x_i.append(Bool(f"x_{i}_{j}"))
            else:
                x_i.append(None)
        x.append(x_i)
    
    u = [Int(f"u_{i}") for i in range(0, 9)]
    
    arrival_time = [Int(f"arrival_{i}") for i in range(0, 9)]
    departure_time = [Int(f"departure_{i}") for i in range(0, 9)]
    
    opt.add(u[0] == 0)
    opt.add(arrival_time[0] == 0)
    opt.add(departure_time[0] == 0)
    
    for i in range(0, 9):
        opt.add(arrival_time[i] >= 0)
        opt.add(arrival_time[i] <= 750)
        opt.add(departure_time[i] >= 0)
        opt.add(departure_time[i] <= 750)
        opt.add(u[i] >= 0)
        opt.add(u[i] <= 8)
    
    # Ensure Union Square has exactly one outgoing edge
    outgoing_0 = []
    for j in range(1, 9):
        j_index = j - 1
        if x[0][j_index] is not None:
            outgoing_0.append(x[0][j_index])
    opt.add(Sum([If(edge, 1, 0) for edge in outgoing_0]) == 1)
    
    # Total edges should equal number of met friends
    total_edges = []
    for i in range(0, 9):
        for j_index in range(0, 8):
            if x[i][j_index] is not None:
                total_edges.append(x[i][j_index])
    opt.add(Sum([If(edge, 1, 0) for edge in total_edges]) == Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    for j in range(1, 9):
        j_index_in_meet = j - 1
        
        incoming_edges = []
        for i in range(0, 9):
            if i != j and x[i][j_index_in_meet] is not None:
                incoming_edges.append(x[i][j_index_in_meet])
        opt.add(meet[j_index_in_meet] == Or(incoming_edges))
        
        opt.add(If(meet[j_index_in_meet], 
                   Sum([If(x[i][j_index_in_meet], 1, 0) for i in range(0,9) if i != j and x[i][j_index_in_meet] is not None]) == 1, 
                   True))
        
        opt.add(If(Not(meet[j_index_in_meet]), 
                   Sum([If(x[i][j_index_in_meet], 1, 0) for i in range(0,9) if i != j and x[i][j_index_in_meet] is not None]) == 0, 
                   True))
        
        for i in range(0, 9):
            if i != j and x[i][j_index_in_meet] is not None:
                opt.add(Implies(x[i][j_index_in_meet], u[j] == u[i] + 1))
        
        for i in range(0, 9):
            if i != j and x[i][j_index_in_meet] is not None:
                opt.add(Implies(x[i][j_index_in_meet], arrival_time[j] == departure_time[i] + travel_time[i][j]))
        
        start_time_j = If(arrival_time[j] >= available_start[j], arrival_time[j], available_start[j])
        opt.add(Implies(meet[j_index_in_meet], departure_time[j] == start_time_j + min_duration[j]))
        opt.add(Implies(meet[j_index_in_meet], departure_time[j] <= available_end[j]))
        opt.add(Implies(meet[j_index_in_meet], start_time_j >= available_start[j]))
        opt.add(Implies(meet[j_index_in_meet], start_time_j + min_duration[j] <= available_end[j]))
    
    objective = Sum([If(meet_i, 1, 0) for meet_i in meet])
    opt.maximize(objective)
    
    if opt.check() == sat:
        m = opt.model()
        num_met = m.evaluate(objective)
        print(f"Number of friends met: {num_met}")
        
        print("\nSchedule:")
        # Reconstruct path by following edges
        path = [0]
        current = 0
        while True:
            next_node = None
            for j in range(1, 9):
                j_index = j - 1
                if current != j:
                    if current == 0:
                        if x[0][j_index] is not None:
                            if m.evaluate(x[0][j_index]):
                                next_node = j
                                break
                    else:
                        if x[current][j_index] is not None:
                            if m.evaluate(x[current][j_index]):
                                next_node = j
                                break
            if next_node is None or next_node in path:
                break
            path.append(next_node)
            current = next_node
        
        prev_node = 0
        for node in path[1:]:
            travel_time_val = travel_time[prev_node][node]
            
            dep_time_val = m.evaluate(departure_time[node])
            if is_int_value(dep_time_val):
                dep_minutes = dep_time_val.as_long()
                start_minutes = dep_minutes - min_duration[node]
                
                # Format start time
                hours, minutes = divmod(start_minutes, 60)
                start_hour = 9 + hours
                start_ampm = "AM" if start_hour < 12 else "PM"
                if start_hour > 12:
                    start_hour -= 12
                if start_hour == 0:
                    start_hour = 12
                start_time_str = f"{start_hour}:{minutes:02d} {start_ampm}"
                
                # Format end time
                hours, minutes = divmod(dep_minutes, 60)
                end_hour = 9 + hours
                end_ampm = "AM" if end_hour < 12 else "PM"
                if end_hour > 12:
                    end_hour -= 12
                if end_hour == 0:
                    end_hour = 12
                end_time_str = f"{end_hour}:{minutes:02d} {end_ampm}"
            else:
                start_time_str = "???"
                end_time_str = "???"
            
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
            
            print(f"Travel from {prev_node} to {node} took {travel_time_val} minutes.")
            print(f"Meet {friend_name} from {start_time_str} to {end_time_str}.")
            prev_node = node
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()