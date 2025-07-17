from z3 import *

def main():
    # Define the travel time matrix (10x10: indices 0 to 9 for locations)
    travel_matrix = [
        [0, 19, 19, 23, 22, 15, 20, 12, 21, 7],   # 0: Presidio
        [17, 0, 21, 11, 13, 27, 8, 25, 12, 18],    # 1: Fisherman's Wharf
        [17, 19, 0, 17, 14, 16, 16, 9, 15, 11],    # 2: Alamo Square
        [22, 10, 17, 0, 9, 30, 4, 23, 5, 21],      # 3: Financial District
        [24, 15, 15, 9, 0, 27, 11, 22, 7, 20],     # 4: Union Square
        [16, 29, 17, 30, 30, 0, 30, 11, 30, 12],   # 5: Sunset District
        [20, 6, 19, 5, 10, 30, 0, 25, 7, 21],      # 6: Embarcadero
        [11, 24, 9, 26, 22, 10, 25, 0, 23, 7],     # 7: Golden Gate Park
        [19, 8, 17, 5, 7, 29, 5, 23, 0, 20],       # 8: Chinatown
        [7, 18, 13, 22, 21, 11, 19, 9, 20, 0]      # 9: Richmond District
    ]
    
    # Meeting data: [min_start, max_end, min_duration] in minutes from 9:00 AM
    meetings = [
        (75, 240, 90),    # 1: Jeffrey (Fisherman's Wharf)
        (0, 345, 120),    # 2: Ronald (Alamo Square) - window starts at 7:45AM, effective start at 0 (9:00AM)
        (105, 420, 105),  # 3: Jason (Financial District)
        (525, 555, 15),   # 4: Melissa (Union Square)
        (345, 510, 105),  # 5: Elizabeth (Sunset District)
        (255, 600, 90),   # 6: Margaret (Embarcadero)
        (600, 780, 75),   # 7: George (Golden Gate Park)
        (30, 720, 15),    # 8: Richard (Chinatown)
        (45, 540, 60)     # 9: Laura (Richmond District)
    ]
    
    n_nodes = 10  # 0 to 9: Presidio and 9 friend locations
    n_meetings = 9  # 9 friends
    sink = 10  # sink node index
    
    s = Solver()
    
    # x[i][j]: if we travel from node i to node j (j can be sink=10)
    x = []
    for i in range(n_nodes):
        row = []
        for j in range(n_nodes + 1):  # j from 0 to 10
            if i == j:
                row.append(Bool(f"x_{i}_{j}"))  # will be set to False later
            else:
                row.append(Bool(f"x_{i}_{j}"))
        x.append(row)
    
    # visited[i] for meeting nodes 1 to 9 (index 0 to 8 in visited list)
    visited = [Bool(f"visited_{i+1}") for i in range(n_meetings)]
    
    # time_var[i]: time arriving at node i (for i in 0..9)
    time_var = [Real(f"time_{i}") for i in range(n_nodes)]
    
    # For meeting nodes 1..9: start and end times
    start_var = [Real(f"start_{i+1}") for i in range(n_meetings)]
    end_var = [Real(f"end_{i+1}") for i in range(n_meetings)]
    
    # u[i] for MTZ (for i in 0..9)
    u = [Int(f"u_{i}") for i in range(n_nodes)]
    
    # Constraints:
    
    # 1. Start at node0 (Presidio): time0 = 0, u0 = 0
    s.add(time_var[0] == 0)
    s.add(u[0] == 0)
    
    # 2. Exactly one outgoing edge from start (node0) to j in 1..10
    s.add(Sum([x[0][j] for j in range(1, n_nodes + 1)]) == 1)
    
    # 3. No self loops: for any i, x[i][i] is False
    for i in range(n_nodes):
        s.add(x[i][i] == False)
    
    # 4. For meeting nodes i in 1..9 (index 1 to 9 in node index, and meetings[i-1] for meeting data)
    for i in range(1, n_nodes):  # node index i from 1 to 9
        # visited[i-1] corresponds to the meeting at node i (since visited index: node1 is at index0 in visited list)
        s.add(visited[i-1] == Or([x[j][i] for j in range(0, n_nodes) if j != i]))
        
        # If visited, then one incoming and one outgoing edge (excluding self and sink for outgoing includes sink)
        s.add(If(visited[i-1],
                 And(
                     Sum([If(x[j][i], 1, 0) for j in range(0, n_nodes) if j != i]) == 1,
                     Sum([If(x[i][j], 1, 0) for j in range(0, n_nodes+1) if j != i]) == 1
                 ),
                 And(
                     Sum([If(x[j][i], 1, 0) for j in range(0, n_nodes) if j != i]) == 0,
                     Sum([If(x[i][j], 1, 0) for j in range(0, n_nodes+1) if j != i]) == 0
                 )))
        
        # Time constraints for the meeting at node i (if visited)
        meeting_idx = i-1  # index in meetings list
        min_start, max_end, min_dur = meetings[meeting_idx]
        s.add(If(visited[i-1],
                 And(
                     start_var[i-1] == If(time_var[i] >= min_start, time_var[i], min_start),
                     end_var[i-1] == start_var[i-1] + min_dur,
                     end_var[i-1] <= max_end
                 ),
                 True))
        
        # MTZ: if visited, then u[i] is between 1 and 9
        s.add(If(visited[i-1], And(u[i] >= 1, u[i] <= n_meetings), True))
    
    # 5. For edges: from i to j (j in 1..9 or sink)
    for i in range(0, n_nodes):
        for j in range(0, n_nodes + 1):
            if i == j:
                continue
            if j < n_nodes:  # j is a node in 0..9
                if j == 0:
                    # We do not allow any edge to node0 (start) except from sink? We don't want to go back to start.
                    s.add(x[i][j] == False)
                else:
                    # j in 1..9
                    s.add(If(x[i][j],
                             And(
                                 time_var[j] == If(i == 0, 
                                                   time_var[i] + travel_matrix[i][j], 
                                                   end_var[i-1] + travel_matrix[i][j]),
                                 u[j] == If(i == 0, 1, u[i] + 1)
                             ),
                             True))
            else:
                # j is sink (10)
                s.add(If(x[i][j], 
                         True, 
                         True))
    
    # 6. Additional MTZ: ensure distinct u for visited nodes? 
    # Since we set u[j] = u[i] + 1 for edges, and u0=0, and u for meetings>=1, it should be distinct naturally.
    
    # Objective: maximize the number of visited meetings
    total_visited = Sum([If(v, 1, 0) for v in visited])
    s.maximize(total_visited)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        total_met = model.eval(total_visited)
        print(f"Total friends met: {total_met}")
        
        # Reconstruct the path
        path = []
        current = 0  # start at Presidio
        while current != sink:
            next_node = None
            for j in range(0, n_nodes + 1):
                if j == current:
                    continue
                if is_true(model[x[current][j]]):
                    next_node = j
                    break
            if next_node is None:
                break
            if next_node == sink:
                break
            path.append(next_node)
            current = next_node
        
        # Print the schedule
        print("Schedule:")
        current_time_minutes = 0  # start at 9:00 AM (0 minutes)
        current_location = 0  # Presidio
        for node in path:
            # Travel to node
            travel_time = travel_matrix[current_location][node]
            arrival_time = current_time_minutes + travel_time
            # Get meeting data
            meeting_idx = node - 1
            min_start, max_end, min_dur = meetings[meeting_idx]
            # Start time is max(arrival_time, min_start)
            start_time = max(arrival_time, min_start)
            end_time = start_time + min_dur
            # Convert times to HH:MM
            def to_time(minutes):
                hours = 9 + minutes // 60
                mins = minutes % 60
                return f"{int(hours):02d}:{int(mins):02d}"
            
            location_names = [
                "Presidio",
                "Fisherman's Wharf (Jeffrey)",
                "Alamo Square (Ronald)",
                "Financial District (Jason)",
                "Union Square (Melissa)",
                "Sunset District (Elizabeth)",
                "Embarcadero (Margaret)",
                "Golden Gate Park (George)",
                "Chinatown (Richard)",
                "Richmond District (Laura)"
            ]
            print(f"Travel from {location_names[current_location]} to {location_names[node]}: {travel_time} minutes.")
            print(f"  Arrive at {to_time(arrival_time)}")
            print(f"  Meeting starts at {to_time(start_time)}, ends at {to_time(end_time)} (duration: {min_dur} minutes)")
            current_time_minutes = end_time
            current_location = node
        
        # Print which friends were met
        for i in range(n_meetings):
            if is_true(model[visited[i]]):
                print(f"Met friend at {location_names[i+1]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()