from z3 import *
import json

def main():
    # Locations: 0:Presidio, 1:Jeffrey (Fisherman's Wharf), 2:Ronald (Alamo Square), 3:Jason (Financial District),
    # 4:Melissa (Union Square), 5:Elizabeth (Sunset District), 6:Margaret (Embarcadero), 
    # 7:George (Golden Gate Park), 8:Richard (Chinatown), 9:Laura (Richmond District)
    travel_time = [
        [0, 19, 19, 23, 22, 15, 20, 12, 21, 7],    # from Presidio (0)
        [17, 0, 21, 11, 13, 27, 8, 25, 12, 18],     # from Fisherman's Wharf (1)
        [17, 19, 0, 17, 14, 16, 16, 9, 15, 11],     # from Alamo Square (2)
        [22, 10, 17, 0, 9, 30, 4, 23, 5, 21],       # from Financial District (3)
        [24, 15, 15, 9, 0, 27, 11, 22, 7, 20],      # from Union Square (4)
        [16, 29, 17, 30, 30, 0, 30, 11, 30, 12],    # from Sunset District (5)
        [20, 6, 19, 5, 10, 30, 0, 25, 7, 21],       # from Embarcadero (6)
        [11, 24, 9, 26, 22, 10, 25, 0, 23, 7],      # from Golden Gate Park (7)
        [19, 8, 17, 5, 7, 29, 5, 23, 0, 20],        # from Chinatown (8)
        [7, 18, 13, 22, 21, 11, 19, 9, 20, 0]       # from Richmond District (9)
    ]
    
    # Meetings: [available_start, available_end, min_duration] in minutes since midnight
    meetings = [
        [10*60+15, 13*60+0, 90],    # Jeffrey (1)
        [7*60+45, 14*60+45, 120],   # Ronald (2)
        [10*60+45, 16*60+0, 105],   # Jason (3)
        [17*60+45, 18*60+15, 15],   # Melissa (4)
        [14*60+45, 17*60+30, 105],  # Elizabeth (5)
        [13*60+15, 19*60+0, 90],    # Margaret (6)
        [19*60+0, 22*60+0, 75],     # George (7)
        [9*60+30, 21*60+0, 15],     # Richard (8)
        [9*60+45, 18*60+0, 60]      # Laura (9)
    ]
    
    # Names of friends in order of meeting index 1..9
    names = [
        "Jeffrey", "Ronald", "Jason", "Melissa", "Elizabeth", 
        "Margaret", "George", "Richard", "Laura"
    ]
    
    n_meetings = 9
    start_time_base = 9*60  # 9:00 AM in minutes since midnight (540)
    
    # Create Z3 variables
    included = [Bool(f"included_{i}") for i in range(n_meetings)]
    x = [[Bool(f"x_{i}_{j}") for j in range(1, 11)] for i in range(0, 10)]
    A = [Int(f"A_{i}") for i in range(n_meetings)]  # arrival time at meeting i
    S = [Int(f"S_{i}") for i in range(n_meetings)]  # start time of meeting i
    E = [Int(f"E_{i}") for i in range(n_meetings)]  # end time of meeting i
    u = [Int(f"u_{i}") for i in range(n_meetings)]  # MTZ: position in the path for meeting i
    
    opt = Optimize()
    
    # Flow constraints: start node (0) to exactly one node (meeting or end)
    out_start = []
    for j in range(0, 9):  # j from 0 to 8: meetings 1..9 (index j in x: j from 0 to 8 corresponds to node j+1)
        out_start.append(x[0][j])
    out_start.append(x[0][9])  # to end node (index 9 in x is the end node, which is j=10 in our 1..10, here index 9)
    opt.add(Sum([If(x0, 1, 0) for x0 in out_start]) == 1)
    
    # End node: exactly one incoming edge
    in_end = [x[i][9] for i in range(0, 10)]  # from any node i (0..9) to end (index 9 in x, which is j=10)
    opt.add(Sum([If(ie, 1, 0) for ie in in_end]) == 1)
    
    # For each meeting j (index 0..8 for meetings 1..9)
    for j in range(n_meetings):
        # In_degree: from any node i (0..9) to meeting j (which is j+1, so in x the column index is j for meeting j+1? 
        # In our x, for meeting j (0-indexed) corresponds to node j+1, so the column index in x is j (for j in 0..8) and the end is at column 9.
        in_edges = []
        for i in range(0, 10):  # i from 0 to 9
            if i != j+1:  # node j+1 is the meeting node, and i is the predecessor node index (0..9)
                in_edges.append(x[i][j])  # x[i][j] for meeting j (node j+1) in column j
        # The meeting j is included if and only if there is one incoming edge
        opt.add(Sum([If(ie, 1, 0) for ie in in_edges]) == If(included[j], 1, 0))
        
        # Out_degree: from meeting j (node j+1) to any node k (meetings 1..9 or end)
        out_edges = []
        for k in range(0, 10):  # k from 0 to 9: meetings 1..9 are k in 0..8, end is k=9
            if k != j:  # but note: we are at node j+1, and we are going to node (k+1) if k<9, or end if k=9
                # We avoid self-loop: j+1 to j+1 is not allowed, so when k = j, skip? But k=j means going to meeting j+1 again? 
                # Actually, k is the column index: column k for k in 0..8 is meeting node k+1, and k=9 is end.
                # We are at node j+1, we can go to any node except itself.
                # So skip when the target node is the same as current node: i.e., when k = j? But if j=0, k=0: that is from meeting1 to meeting1? skip.
                out_edges.append(x[j+1][k])
        # The meeting j is included if and only if there is one outgoing edge
        opt.add(Sum([If(oe, 1, 0) for oe in out_edges]) == If(included[j], 1, 0))
    
    # MTZ constraints: 
    for j in range(n_meetings):
        opt.add(If(included[j], And(u[j] >= 1, u[j] <= 9), True))
    
    # Constraints from start: if we go from start (0) to meeting j (node j+1, column j in x[0]), then u[j] = 1
    for j in range(n_meetings):
        opt.add(If(And(included[j], x[0][j]), u[j] == 1, True))
    
    # Constraints between meetings: if we go from meeting i (node i+1) to meeting j (node j+1), and both are included, then u[j] = u[i] + 1
    for i in range(n_meetings):
        for j in range(n_meetings):
            if i != j:
                # x[i+1][j] is the edge from node i+1 to node j+1 (which is in column j of row i+1)
                opt.add(If(And(included[i], included[j], x[i+1][j]), u[j] == u[i] + 1, True))
    
    # Time constraints for each meeting
    for j in range(n_meetings):
        # If meeting j is included, then:
        #   A[j] = sum over i: if x[i][j] then (if i==0: start_time_base + travel_time[0][j+1] else E[i-1] + travel_time[i][j+1])
        #   But note: i in [0,1,...,9] (nodes) and j in x is column j (for meeting j+1)
        #   For i=0: we use start_time_base + travel_time[0][j+1]
        #   For i>=1: then meeting i-1 (because i is node index, which corresponds to meeting index = i-1) must be included and we use E[i-1] + travel_time[i][j+1]
        terms = []
        for i in range(0, 10):  # i from 0 to 9: the predecessor node
            if i == 0:
                term = If(x[i][j], start_time_base + travel_time[0][j+1], 0)
            else:
                # i>=1: then this predecessor is meeting node i, which corresponds to meeting index i-1
                term = If(x[i][j], E[i-1] + travel_time[i][j+1], 0)
            terms.append(term)
        total_arrival = Sum(terms)
        opt.add(If(included[j], A[j] == total_arrival, True))
        
        # Meeting j must start at or after arrival and at or after available_start, and end = start + duration, and end before available_end.
        opt.add(If(included[j], 
                  And(
                      S[j] >= A[j],
                      S[j] >= meetings[j][0],
                      E[j] == S[j] + meetings[j][2],
                      E[j] <= meetings[j][1]
                  ), 
                  True))
    
    # Objective: maximize the number of included meetings
    total_included = Sum([If(incl, 1, 0) for incl in included])
    opt.maximize(total_included)
    
    # Solve the model
    if opt.check() == sat:
        model = opt.model()
        # Reconstruct the path
        current = 0  # start at node0 (Presidio)
        itinerary = []
        # We'll follow the path until we hit the end node (10, which is index9 in x columns)
        # Map meeting index to name: meeting j (0-indexed) is names[j]
        while True:
            next_node = None
            for j in range(0, 10):  # j: columns 0..9: meetings 1..9 (j in 0..8) and end (j=9)
                if current < 10:  # current is a node index (0..9)
                    if model.evaluate(x[current][j]):
                        next_node = j
                        break
            if next_node is None:
                break
            if next_node == 9:  # end node
                break
            # next_node is in [0,1,...,8] -> meeting node next_node+1, but the meeting index is next_node
            meeting_index = next_node  # because meetings are 0..8 for next_node 0..8
            if model.evaluate(included[meeting_index]):
                start_val = model.evaluate(S[meeting_index])
                end_val = model.evaluate(E[meeting_index])
                # Convert to integers
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                # Convert to HH:MM
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[meeting_index],
                    "start_time": start_str,
                    "end_time": end_str
                })
            current = next_node + 1  # because the meeting node is next_node+1 (since node1 is meeting0, node2 is meeting1, ...) 
            # But in our x, the next_node is the column index, which for meeting j is the meeting node j+1. 
            # So after visiting meeting j (which is at node j+1), we set current to j+1 (the node index) to find the next.
        # Output the itinerary
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()