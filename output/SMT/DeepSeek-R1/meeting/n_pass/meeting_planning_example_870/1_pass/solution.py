import z3
import json

def main():
    # Define the travel times as a multi-line string
    travel_data = """
    Pacific Heights to Marina District: 6.
    Pacific Heights to The Castro: 16.
    Pacific Heights to Richmond District: 12.
    Pacific Heights to Alamo Square: 10.
    Pacific Heights to Financial District: 13.
    Pacific Heights to Presidio: 11.
    Pacific Heights to Mission District: 15.
    Pacific Heights to Nob Hill: 8.
    Pacific Heights to Russian Hill: 7.
    Marina District to Pacific Heights: 7.
    Marina District to The Castro: 22.
    Marina District to Richmond District: 11.
    Marina District to Alamo Square: 15.
    Marina District to Financial District: 17.
    Marina District to Presidio: 10.
    Marina District to Mission District: 20.
    Marina District to Nob Hill: 12.
    Marina District to Russian Hill: 8.
    The Castro to Pacific Heights: 16.
    The Castro to Marina District: 21.
    The Castro to Richmond District: 16.
    The Castro to Alamo Square: 8.
    The Castro to Financial District: 21.
    The Castro to Presidio: 20.
    The Castro to Mission District: 7.
    The Castro to Nob Hill: 16.
    The Castro to Russian Hill: 18.
    Richmond District to Pacific Heights: 10.
    Richmond District to Marina District: 9.
    Richmond District to The Castro: 16.
    Richmond District to Alamo Square: 13.
    Richmond District to Financial District: 22.
    Richmond District to Presidio: 7.
    Richmond District to Mission District: 20.
    Richmond District to Nob Hill: 17.
    Richmond District to Russian Hill: 13.
    Alamo Square to Pacific Heights: 10.
    Alamo Square to Marina District: 15.
    Alamo Square to The Castro: 8.
    Alamo Square to Richmond District: 11.
    Alamo Square to Financial District: 17.
    Alamo Square to Presidio: 17.
    Alamo Square to Mission District: 10.
    Alamo Square to Nob Hill: 11.
    Alamo Square to Russian Hill: 13.
    Financial District to Pacific Heights: 13.
    Financial District to Marina District: 15.
    Financial District to The Castro: 20.
    Financial District to Richmond District: 21.
    Financial District to Alamo Square: 17.
    Financial District to Presidio: 22.
    Financial District to Mission District: 17.
    Financial District to Nob Hill: 8.
    Financial District to Russian Hill: 11.
    Presidio to Pacific Heights: 11.
    Presidio to Marina District: 11.
    Presidio to The Castro: 21.
    Presidio to Richmond District: 7.
    Presidio to Alamo Square: 19.
    Presidio to Financial District: 23.
    Presidio to Mission District: 26.
    Presidio to Nob Hill: 18.
    Presidio to Russian Hill: 14.
    Mission District to Pacific Heights: 16.
    Mission District to Marina District: 19.
    Mission District to The Castro: 7.
    Mission District to Richmond District: 20.
    Mission District to Alamo Square: 11.
    Mission District to Financial District: 15.
    Mission District to Presidio: 25.
    Mission District to Nob Hill: 12.
    Mission District to Russian Hill: 15.
    Nob Hill to Pacific Heights: 8.
    Nob Hill to Marina District: 11.
    Nob Hill to The Castro: 17.
    Nob Hill to Richmond District: 14.
    Nob Hill to Alamo Square: 11.
    Nob Hill to Financial District: 9.
    Nob Hill to Presidio: 17.
    Nob Hill to Mission District: 13.
    Nob Hill to Russian Hill: 5.
    Russian Hill to Pacific Heights: 7.
    Russian Hill to Marina District: 7.
    Russian Hill to The Castro: 21.
    Russian Hill to Richmond District: 14.
    Russian Hill to Alamo Square: 15.
    Russian Hill to Financial District: 11.
    Russian Hill to Presidio: 14.
    Russian Hill to Mission District: 16.
    Russian Hill to Nob Hill: 5.
    """

    # Parse the travel data
    travel_time_dict = {}
    lines = travel_data.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        parts = line.split(':')
        if len(parts) < 2:
            continue
        from_to = parts[0].split(' to ')
        if len(from_to) < 2:
            continue
        from_dist = from_to[0].strip()
        to_dist = from_to[1].strip()
        time_str = parts[1].strip().rstrip('.')
        try:
            time_val = int(time_str)
        except:
            continue
        
        if from_dist not in travel_time_dict:
            travel_time_dict[from_dist] = {}
        travel_time_dict[from_dist][to_dist] = time_val

    # Ensure all districts are in the dictionary
    districts_list = [
        "Pacific Heights",
        "Marina District",
        "The Castro",
        "Richmond District",
        "Alamo Square",
        "Financial District",
        "Presidio",
        "Mission District",
        "Nob Hill",
        "Russian Hill"
    ]
    for d1 in districts_list:
        if d1 not in travel_time_dict:
            travel_time_dict[d1] = {}
        for d2 in districts_list:
            if d1 == d2:
                continue
            if d2 not in travel_time_dict[d1]:
                print(f"Warning: missing travel time from {d1} to {d2}")

    # Friend data: index, name, district, available_start, available_end, min_duration
    # Times in minutes after 9:00 AM
    friends = [
        # Linda: Marina District from 18:00 to 22:00, 30 min
        {"name": "Linda", "district": "Marina District", "start": 540, "end": 780, "min_duration": 30},
        # Kenneth: The Castro from 14:45 to 16:15, 30 min
        {"name": "Kenneth", "district": "The Castro", "start": 345, "end": 435, "min_duration": 30},
        # Kimberly: Richmond District from 14:15 to 22:00, 30 min
        {"name": "Kimberly", "district": "Richmond District", "start": 315, "end": 780, "min_duration": 30},
        # Paul: Alamo Square from 21:00 to 21:30, 15 min
        {"name": "Paul", "district": "Alamo Square", "start": 720, "end": 750, "min_duration": 15},
        # Carol: Financial District from 10:15 to 12:00, 60 min
        {"name": "Carol", "district": "Financial District", "start": 75, "end": 180, "min_duration": 60},
        # Brian: Presidio from 10:00 to 21:30, 75 min
        {"name": "Brian", "district": "Presidio", "start": 60, "end": 750, "min_duration": 75},
        # Laura: Mission District from 16:15 to 20:30, 30 min
        {"name": "Laura", "district": "Mission District", "start": 435, "end": 690, "min_duration": 30},
        # Sandra: Nob Hill from 9:15 to 18:30, 60 min
        {"name": "Sandra", "district": "Nob Hill", "start": 15, "end": 570, "min_duration": 60},
        # Karen: Russian Hill from 18:30 to 22:00, 75 min
        {"name": "Karen", "district": "Russian Hill", "start": 570, "end": 780, "min_duration": 75}
    ]
    n_friends = len(friends)

    # Extract districts for meetings
    districts = [friend["district"] for friend in friends]

    # Z3 solver setup
    solver = z3.Solver()
    # solver.set("timeout", 300000)  # 5 minutes timeout

    # Variables
    selected = [z3.Bool(f"selected_{i}") for i in range(n_friends)]
    # We have 10 nodes: 0 = start (Pacific Heights), 1..9 = meetings (index 0..8), 10 = end node (index9)
    # succ[i] for i in 0..9 (node indices 0 to 9, where node9 is the end node, and node10 is not used as a source)
    succ = [z3.Int(f"succ_{i}") for i in range(10)]  # for node0 to node9 (the end node is 9)
    s = [z3.Real(f"s_{i}") for i in range(n_friends)]  # start times for meetings
    e = [s[i] + friends[i]["min_duration"] for i in range(n_friends)]  # end times for meetings
    dist = [z3.Int(f"dist_{i}") for i in range(10)]   # for node0 to node9

    # Constraints

    # 1. Domain for succ[0] (start node): must be in [0, 8] (meetings) or 9 (end)
    solver.add(succ[0] >= 0, succ[0] <= 9)
    # If a meeting i is selected, then if succ[0] == i, then selected[i] must be true.
    for i in range(n_friends):
        solver.add(z3.Implies(succ[0] == i, selected[i]))

    # 2. For each meeting node i (0..8) (which corresponds to friend index i)
    for i in range(n_friends):
        # Domain for succ[i+0] (since our meetings are indexed 0..8, and we are in node i in the path, but note: node0 is start, nodes1..9 are meetings? 
        # Actually, in our path node indexing: 
        #   node0: start
        #   node1 to node9: not used. Instead, we have 9 meetings, and we use the same index for the meeting and the node? 
        #   But we have 10 nodes: 0 (start) and 1..9 for the end? 
        #   We defined: 
        #       node0: start
        #       for meeting i (0-indexed friend), we use the same index i for the node? 
        #   But we have 9 meetings, so nodes 1..9 are not used. Instead, we have only 10 nodes: 0 (start), and then 0..8 for meetings? 
        #   But then node9 is the end.
        #   So meeting i is at node i? 
        #   And we have 10 nodes: 0 (start), 0..8 (meetings), and 9 (end). But this causes duplicate indices for meeting0 and node0 (start). 
        #   Let me redefine: 
        #       We have 10 nodes: 
        #           node0: start (Pacific Heights)
        #           node1 to node9: not used? 
        #       Instead, we have:
        #           node0: start
        #           node1 to node9: we don't have that many. 
        #   Correction: we have:
        #       meetings: 0 to 8 (9 meetings) -> we use the index in the friends array for the meeting.
        #       But in the path, we have:
        #           node0: start
        #           meetings: we have 9 possible meetings, each meeting i is represented by node (i+1)? 
        #       This complicates. 
        #   Let's change: 
        #       We have:
        #         node0: start
        #         node1: meeting0 (Linda)
        #         node2: meeting1 (Kenneth)
        #         ... 
        #         node9: meeting8 (Karen)
        #         node10: end node.
        #   But then we have 11 nodes. 
        #   We defined only 10 nodes in `succ` and `dist` (0..9). 
        #   We must adjust: 
        #       Instead, we can use:
        #           node0: start
        #           node1 to node9: meetings (for friend0 to friend8)
        #           node10: end -> but we only defined up to 9.
        #   We'll redefine to have 11 nodes: 
        #       We did not. 
        #   We'll stick with 10 nodes: 
        #       node0: start
        #       node1 to node9: meetings? Then we have 9 meetings, so node1 to node9 for meetings 0 to 8? 
        #       But then the meeting index and node index are off by one. 
        #   To avoid confusion, we change the model: 
        #       We have:
        #         n = 9 meetings -> 9 nodes for meetings, plus start node (0) and end node (10) -> total 11 nodes.
        #   But we defined `succ` for 10 nodes (0..9). 
        #   We'll redefine the problem to use 11 nodes (0 to 10). 
        #   But the code above for `succ` and `dist` is for 10 nodes. 
        #   Given the time, we adjust: 
        #       We have only 9 meetings. We can let:
        #         node0: start
        #         node1 to node9: meetings (for 9 meetings, but we have only 9 meetings) -> so node1 for meeting0, node9 for meeting8.
        #         node10: end -> but we defined `succ` for 0..9. 
        #   We'll redefine the end node as 9 (so we have 10 nodes: 0..9). 
        #   And the meetings: meeting0 will be node1? 
        #   This complicates the mapping. 
        #   Alternative: 
        #       We map meeting i to node i (so node0 to node8 for meetings). But then we have:
        #         node0: start (Pacific Heights) -> we call it node0
        #         meetings: node1 to node9? 
        #       But we have 9 meetings -> we need 9 nodes for meetings, so total nodes: 1 (start) + 9 (meetings) + 1 (end) = 11.
        #   We change the `succ` and `dist` to have 11 elements (0 to 10). 
        #   But we defined 10. 
        #   We'll adjust the code to have 11 nodes. 
        #   How many nodes? 0 (start), 1..9 (meetings), 10 (end). 
        #   We'll change the range to 11.
        pass  # We are not changing now due to time, so we use the original plan: meetings are indexed 0..8, and nodes 0 (start), 0..8 (meetings), and 9 (end).

        # We'll proceed with the original plan: 
        #   There are 10 nodes: 
        #       node0: start
        #       node1 to node9: not used as indices for meetings? 
        #   Actually, we have meetings 0..8, so we use node0 for start, and then for meeting i we use node i? 
        #   But then meeting0 is at node0? which is the same as start? 
        #   We must separate. 
        #   We decide: 
        #       Let the start node be node0.
        #       Meetings: meeting0 (Linda) is at node1, meeting1 (Kenneth) at node2, ... meeting8 (Karen) at node9.
        #       End node is node10 -> but we only have up to 9 in `succ` (which we defined for 10 nodes: 0..9). 
        #   So we use node10 as the end node? Then we need 11 nodes. 
        #   We'll redefine: 
        n_nodes = 11  # 0 to 10: 0=start, 1..9=meetings, 10=end.
        # But we already defined `succ` and `dist` for 10 nodes. 
        #   We'll change the code to use 11 nodes. 
        #   We'll redefine the variables for 11 nodes. 
    # Due to the complexity, we revert to the initial model that uses 10 nodes (0 to 9) for start, meetings (0..8) and end (9) but note: meeting0 is at node0? 
    # This causes confusion. 

    # Given the time constraints, we change the model: 
    #   We have 10 nodes: node0 to node9.
    #   node0: start (Pacific Heights)
    #   node1 to node9: meetings for friend0 to friend8? 
    #   But then we have 9 meetings, so we use node1 to node9 for meetings. 
    #   And the end node is not explicitly numbered? We can use node0 as start and meetings as node1 to node9, and then the end node is not needed? 
    #   But we need an end node to terminate the path. 
    #   We can introduce node10 as end, but we only have 10 nodes in our arrays. 
    #   We decide to use node9 as the end node. And we have 9 meetings, so meetings are node1 to node9? 
    #   But then we have to map friend0 to node1, etc. 
    #   This makes the code complicated. 

    # We abandon the explicit node indices for meetings and use the meeting index (0..8) for the meetings. 
    #   node0: start
    #   meetings: 0..8 (node0 is start, so meetings are not node0) -> we use node1 to node9 for meetings? 
    #   But then the mapping between meeting index i and node index is i+1. 
    #   We'll do that. 

    #   Let:
    #       start node: node0
    #       meeting i: node i+1   (i in 0..8)
    #       end node: node10 (index 10) -> but we defined `succ` for 0..9. 
    #   We change the number of nodes to 11: 
    n_nodes = 11  # 0..10: 0=start, 1..9=meetings, 10=end.
    # But we already defined `succ` and `dist` for 10 nodes. We will change:
    succ = [z3.Int(f"succ_{i}") for i in range(n_nodes)]
    dist = [z3.Int(f"dist_{i}") for i in range(n_nodes)]

    # Now, for a meeting i (0..8), it is represented by node i+1.
    #   The district for meeting i is districts[i] = friends[i]["district"]
    #   The selected[i] is for meeting i.

    # Constraints for the start node (0):
    solver.add(succ[0] >= 1, succ[0] <= 10)  # next from start must be a meeting (1..9) or end (10)
    for i in range(n_friends):
        # if the next from start is node i+1, then meeting i must be selected.
        solver.add(z3.Implies(succ[0] == i+1, selected[i]))

    # For each meeting node j (j from 1 to 9) (which corresponds to friend i = j-1)
    for j in range(1, 1+n_friends):  # j in [1,9]
        i = j-1   # friend index
        # If the meeting is selected, then succ[j] should be in [1..9] (another meeting) or 10 (end), and not j.
        # Also, if it's not selected, then we set succ[j] to 10 (arbitrarily) to avoid constraints.
        solver.add(z3.Implies(selected[i], 
                              z3.And(succ[j] >= 1, succ[j] <= 10, succ[j] != j,
                                     z3.Implies(succ[j] <= 9, selected[succ[j]-1])
                              )))
        solver.add(z3.Implies(z3.Not(selected[i]), succ[j] == 10))

    # For the end node (10), we don't set its successor. We can set to 10 (self) or any, but not used.
    solver.add(succ[10] == 10)  # self loop, but not necessary

    # Distances: 
    solver.add(dist[0] == 0)
    for j in range(1, 1+n_friends):
        i = j-1
        # If the meeting i is selected, then the distance to its successor is dist[j] + 1
        solver.add(z3.Implies(selected[i], dist[succ[j]] == dist[j] + 1))
    # For the start node: always selected in the path.
    solver.add(dist[succ[0]] == dist[0] + 1)
    # For the end node, we require the distance to be the number of selected meetings + 1 (edges = selected meetings + 1)
    num_selected = z3.Sum([z3.If(selected[i], 1, 0) for i in range(n_friends)])
    solver.add(dist[10] == num_selected + 1)

    # Meeting time windows
    for i in range(n_friends):
        solver.add(z3.Implies(selected[i], 
                              z3.And(s[i] >= friends[i]["start"],
                                     e[i] <= friends[i]["end"])))

    # Start time constraints for meetings
    for i in range(n_friends):
        # meeting i is at node j = i+1
        j = i+1
        # The meeting's start time must be at least the travel time from the predecessor.
        # The predecessor might be the start node (0) or a meeting node k (1..9).
        constraints = []

        # From start node (0) to this meeting if the edge exists
        constraints.append(z3.If(succ[0] == j,
                                travel_time_dict["Pacific Heights"][districts[i]],
                                0))

        # From any meeting node k (1..9) to this meeting node j, if there's an edge
        for k in range(1, 1+n_friends):
            if k == j:
                continue
            # meeting k corresponds to friend idx = k-1
            idx_k = k-1
            constraints.append(
                z3.If(z3.And(selected[idx_k], succ[k] == j),
                      e[idx_k] + travel_time_dict[districts[idx_k]][districts[i]],
                      0
            )
        # s[i] must be at least the maximum of these constraints, but we do:
        for c in constraints:
            solver.add(s[i] >= c)

        # Also, the meeting cannot start before 0
        solver.add(s[i] >= 0)

    # Maximize the number of selected meetings
    objective = num_selected
    solver.add(dist[10] == num_selected + 1)  # already added, but ensure

    # Set the objective
    optimizer = z3.Optimize()
    optimizer.add(solver.assertions())
    optimizer.maximize(objective)

    # Solve
    result = optimizer.check()
    if result == z3.sat:
        model = optimizer.model()
        selected_meetings = []
        for i in range(n_friends):
            if z3.is_true(model[selected[i]]):
                start_val = model[s[i]]
                # Convert Z3 Real to float
                if isinstance(start_val, z3.RatNum):
                    start_val = start_val.as_fraction()
                    start_val = float(start_val)
                elif isinstance(start_val, z3.IntNum):
                    start_val = start_val.as_long()
                else:
                    start_val = 0.0
                end_val = start_val + friends[i]["min_duration"]
                selected_meetings.append({
                    "index": i,
                    "name": friends[i]["name"],
                    "start": start_val,
                    "end": end_val
                })
        # Sort by start time
        selected_meetings.sort(key=lambda x: x["start"])

        # Format to HH:MM
        itinerary = []
        for meet in selected_meetings:
            total_minutes_start = meet["start"]
            hours_start = int(9 + total_minutes_start // 60)
            minutes_start = int(total_minutes_start % 60)
            start_time = f"{hours_start:02d}:{minutes_start:02d}"

            total_minutes_end = meet["end"]
            hours_end = int(9 + total_minutes_end // 60)
            minutes_end = int(total_minutes_end % 60)
            end_time = f"{hours_end:02d}:{minutes_end:02d}"

            itinerary.append({
                "action": "meet",
                "person": meet["name"],
                "start_time": start_time,
                "end_time": end_time
            })

        # Output in JSON
        output = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()