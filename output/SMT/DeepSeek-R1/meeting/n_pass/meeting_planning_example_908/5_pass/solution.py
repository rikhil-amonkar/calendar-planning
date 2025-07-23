from z3 import *
import datetime

def main():
    # Define travel time matrix between districts
    travel_time = [
        [0, 10, 22, 19, 19, 11, 20, 15, 21, 9, 30],
        [11, 0, 17, 26, 22, 7, 27, 9, 18, 13, 27],
        [23, 19, 0, 31, 15, 14, 21, 11, 7, 22, 15],
        [19, 25, 32, 0, 19, 23, 19, 27, 25, 18, 23],
        [21, 23, 15, 18, 0, 17, 6, 17, 10, 19, 15],
        [11, 7, 14, 23, 17, 0, 21, 7, 14, 10, 23],
        [21, 24, 20, 19, 6, 18, 0, 21, 16, 19, 17],
        [17, 10, 10, 27, 16, 8, 22, 0, 11, 16, 19],
        [22, 18, 7, 27, 10, 13, 16, 9, 0, 21, 11],
        [9, 15, 24, 15, 18, 13, 17, 18, 20, 0, 27],
        [30, 29, 16, 22, 15, 24, 17, 21, 12, 30, 0]
    ]
    
    # Meeting details
    window_start_minutes = [0, 195, 0, 390, 585, 15, 45, 45, 450, 450]
    window_end_minutes = [60, 360, 690, 570, 660, 255, 315, 135, 660, 780]
    min_durations = [30, 75, 15, 45, 60, 30, 45, 45, 120, 105]
    friend_names = {
        1: "Mark",
        2: "Stephanie",
        3: "Betty",
        4: "Lisa",
        5: "William",
        6: "Brian",
        7: "Joseph",
        8: "Ashley",
        9: "Patricia",
        10: "Karen"
    }
    
    # Map meetings to districts
    districts = [1, 2, 3, 4, 5, 6, 7, 9, 8, 10]
    
    # Precompute travel times
    tt = [[0]*10 for _ in range(11)]
    for i in range(11):
        for j in range(10):
            if i == 0:
                tt[i][j] = travel_time[0][districts[j]]
            else:
                tt[i][j] = travel_time[districts[i-1]][districts[j]]
    
    # Setup solver
    s = Optimize()
    n_nodes = 11
    end_node = 11
    
    # Define variables
    next_vars = [Int(f'next_{i}') for i in range(n_nodes)]
    visited = [Bool(f'visited_{i}') for i in range(1, 11)]
    start_time = [Int(f'start_{i}') for i in range(1, 11)]
    end_time = [Int(f'end_{i}') for i in range(1, 11)]
    
    # Path constraints
    for i in range(n_nodes):
        s.add(And(next_vars[i] >= 1, next_vars[i] <= 11))
        # Prevent self-loops for meeting nodes
        if i >= 1:
            s.add(next_vars[i] != i)
    
    # Meeting activation constraints
    for j in range(1, 11):
        idx = j - 1
        s.add(visited[idx] == Or([next_vars[i] == j for i in range(n_nodes)]))
        s.add(Sum([If(next_vars[i] == j, 1, 0) for i in range(n_nodes)]) <= 1)
    
    # Time constraints
    for j in range(1, 11):
        j_idx = j - 1
        constraints = []
        
        # Travel time constraints
        for i in range(n_nodes):
            if i == 0:  # Start node
                constraints.append(
                    Implies(And(visited[j_idx], next_vars[i] == j),
                            start_time[j_idx] >= tt[i][j_idx]
                    )
            else:  # Meeting node
                constraints.append(
                    Implies(And(visited[j_idx], next_vars[i] == j),
                            start_time[j_idx] >= end_time[i-1] + tt[i][j_idx]
                    )
                )
        
        # Availability constraints
        constraints.append(
            Implies(visited[j_idx],
                And(
                    start_time[j_idx] >= window_start_minutes[j_idx],
                    end_time[j_idx] == start_time[j_idx] + min_durations[j_idx],
                    end_time[j_idx] <= window_end_minutes[j_idx]
                )
            )
        )
        s.add(And(*constraints))
    
    # Path connectivity constraints (FIXED SYNTAX HERE)
    for j in range(1, 11):
        j_idx = j - 1
        s.add(Implies(visited[j_idx],
            Or( [next_vars[j] == end_node] + 
                [And(next_vars[j] == k, visited[k-1]) for k in range(1, 11)]
            )
        ))
    
    # Objective: maximize meetings
    total_visited = Sum([If(v, 1, 0) for v in visited])
    s.maximize(total_visited)
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current = model.eval(next_vars[0]).as_long()
        while current != end_node and current is not None:
            meeting_index = current
            idx = meeting_index - 1
            if not model.eval(visited[idx]):
                break
            start_min = model.eval(start_time[idx]).as_long()
            end_min = model.eval(end_time[idx]).as_long()
            
            # Format times
            base_time = datetime.datetime(2023, 1, 1, 9, 0)
            start_str = (base_time + datetime.timedelta(minutes=start_min)).strftime("%H:%M")
            end_str = (base_time + datetime.timedelta(minutes=end_min)).strftime("%H:%M")
            
            itinerary.append({
                "action": "meet",
                "person": friend_names[meeting_index],
                "start_time": start_str,
                "end_time": end_str
            })
            
            current = model.eval(next_vars[meeting_index]).as_long()
        
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()