import z3
from z3 import *

def main():
    # Locations mapping: node index to location name
    locations = {
        0: "Golden Gate Park",
        1: "The Castro",         # Karen
        2: "Alamo Square",       # Deborah
        3: "Chinatown",          # Elizabeth
        4: "Fisherman's Wharf",  # Laura
        5: "North Beach",        # Jason
        6: "Russian Hill",       # Steven
        7: "Haight-Ashbury"      # Carol
    }
    
    # Travel times dictionary from the given data
    travel_tuples = [
        ("Golden Gate Park", "Haight-Ashbury", 7),
        ("Golden Gate Park", "Fisherman's Wharf", 24),
        ("Golden Gate Park", "The Castro", 13),
        ("Golden Gate Park", "Chinatown", 23),
        ("Golden Gate Park", "Alamo Square", 10),
        ("Golden Gate Park", "North Beach", 24),
        ("Golden Gate Park", "Russian Hill", 19),
        ("Haight-Ashbury", "Golden Gate Park", 7),
        ("Haight-Ashbury", "Fisherman's Wharf", 23),
        ("Haight-Ashbury", "The Castro", 6),
        ("Haight-Ashbury", "Chinatown", 19),
        ("Haight-Ashbury", "Alamo Square", 5),
        ("Haight-Ashbury", "North Beach", 19),
        ("Haight-Ashbury", "Russian Hill", 17),
        ("Fisherman's Wharf", "Golden Gate Park", 25),
        ("Fisherman's Wharf", "Haight-Ashbury", 22),
        ("Fisherman's Wharf", "The Castro", 26),
        ("Fisherman's Wharf", "Chinatown", 12),
        ("Fisherman's Wharf", "Alamo Square", 20),
        ("Fisherman's Wharf", "North Beach", 6),
        ("Fisherman's Wharf", "Russian Hill", 7),
        ("The Castro", "Golden Gate Park", 11),
        ("The Castro", "Haight-Ashbury", 6),
        ("The Castro", "Fisherman's Wharf", 24),
        ("The Castro", "Chinatown", 20),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "North Beach", 20),
        ("The Castro", "Russian Hill", 18),
        ("Chinatown", "Golden Gate Park", 23),
        ("Chinatown", "Haight-Ashbury", 19),
        ("Chinatown", "Fisherman's Wharf", 8),
        ("Chinatown", "The Castro", 22),
        ("Chinatown", "Alamo Square", 17),
        ("Chinatown", "North Beach", 3),
        ("Chinatown", "Russian Hill", 7),
        ("Alamo Square", "Golden Gate Park", 9),
        ("Alamo Square", "Haight-Ashbury", 5),
        ("Alamo Square", "Fisherman's Wharf", 19),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "Chinatown", 16),
        ("Alamo Square", "North Beach", 15),
        ("Alamo Square", "Russian Hill", 13),
        ("North Beach", "Golden Gate Park", 22),
        ("North Beach", "Haight-Ashbury", 18),
        ("North Beach", "Fisherman's Wharf", 5),
        ("North Beach", "The Castro", 22),
        ("North Beach", "Chinatown", 6),
        ("North Beach", "Alamo Square", 16),
        ("North Beach", "Russian Hill", 4),
        ("Russian Hill", "Golden Gate Park", 21),
        ("Russian Hill", "Haight-Ashbury", 17),
        ("Russian Hill", "Fisherman's Wharf", 7),
        ("Russian Hill", "The Castro", 21),
        ("Russian Hill", "Chinatown", 9),
        ("Russian Hill", "Alamo Square", 15),
        ("Russian Hill", "North Beach", 5)
    ]
    
    travel_dict = {}
    for (from_loc, to_loc, t) in travel_tuples:
        travel_dict[(from_loc, to_loc)] = t
    
    # Create an 8x8 travel matrix: [i][j] = travel time from node i to node j
    travel_matrix = [[0]*8 for _ in range(8)]
    for i in range(8):
        for j in range(8):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                from_loc = locations[i]
                to_loc = locations[j]
                travel_matrix[i][j] = travel_dict[(from_loc, to_loc)]
    
    # Durations for each meeting (node index: duration in minutes)
    durations = {
        1: 75,   # Karen (The Castro)
        2: 105,   # Deborah (Alamo Square)
        3: 75,    # Elizabeth (Chinatown)
        4: 60,    # Laura (Fisherman's Wharf)
        5: 90,    # Jason (North Beach)
        6: 120,   # Steven (Russian Hill)
        7: 60     # Carol (Haight-Ashbury) - fixed
    }
    
    # Available start and end times (in minutes from 9:00AM)
    avail_start = {
        1: 0,     # Karen: available from 9:00AM (0 minutes) to 2:00PM (300 minutes)
        2: 180,   # Deborah: 12:00PM (180 minutes) to 3:00PM (360 minutes)
        3: 195,   # Elizabeth: 12:15PM (195 minutes) to 9:30PM (750 minutes)
        4: 165,   # Laura: 11:45AM (165 minutes) to 9:30PM (750 minutes)
        5: 345,   # Jason: 2:45PM (345 minutes) to 7:00PM (600 minutes) -> must end by 600
        6: 345    # Steven: 2:45PM (345 minutes) to 6:30PM (570 minutes) -> must end by 570
    }
    avail_end = {
        1: 300,   # Karen: must end by 2:00PM (300 minutes)
        2: 360,   # Deborah: must end by 3:00PM (360 minutes)
        3: 750,   # Elizabeth: must end by 9:30PM (750 minutes)
        4: 750,   # Laura: must end by 9:30PM (750 minutes)
        5: 600,   # Jason: must end by 7:00PM (600 minutes)
        6: 570    # Steven: must end by 6:30PM (570 minutes)
    }
    
    # Initialize Z3 optimizer
    s = Optimize()
    
    # Meet variables for nodes 1 to 6 (Karen to Steven)
    meet = [Bool(f"meet{i}") for i in range(1,7)]  # meet1 to meet6
    
    # Time variables: time1 (node1: Karen) to time7 (node7: Carol)
    time = [Real(f"time{i}") for i in range(1,8)]  # time1 to time7
    
    # Fix Carol's time (node7) to 750 minutes (9:30PM)
    s.add(time[6] == 750)
    
    # Next variables: next[i][j] for i in [0,6] (source nodes: node0 to node6) and j in [0,6] (destination nodes: node1 to node7, where j=0->node1, j=6->node7)
    next_var = [[Bool(f"next_{i}_{j}") for j in range(7)] for i in range(7)]  # 7x7 matrix
    
    # Constraint: Start (node0) has exactly one outgoing edge
    s.add(PbEq([(next_var[0][j], 1) for j in range(7)], 1))
    
    # Constraints for non-Carol meetings (nodes 1 to 6)
    for i_node in range(1,7):  # i_node: the actual node index (1 to 6)
        # Incoming edges: from any source node (0 to 6) to this node i_node
        #   In next_var: the destination node i_node is represented by column = i_node-1 (because j=0->node1, j=1->node2, ..., j=5->node6)
        incoming = [ next_var[src][i_node-1] for src in range(7) ]  # src from 0 to 6
        incoming_count = Sum([If(x, 1, 0) for x in incoming])
        
        # Outgoing edges: from this node i_node (which is row i_node) to any destination node (0 to 6) -> next_var[i_node][j] for j in [0,6]
        outgoing = [ next_var[i_node][j] for j in range(7) ]
        outgoing_count = Sum([If(x, 1, 0) for x in outgoing])
        
        # The meet variable for this node: meet[i_node-1] (since meet[0] is for node1, meet[1] for node2, etc.)
        meet_var = meet[i_node-1]
        
        s.add(If(meet_var, incoming_count == 1, incoming_count == 0))
        s.add(If(meet_var, outgoing_count == 1, outgoing_count == 0))
        
        # Time constraints for the meeting if we meet
        time_var = time[i_node-1]  # time for node i_node (which is stored at time[i_node-1])
        s.add(Implies(meet_var, time_var >= avail_start[i_node]))
        s.add(Implies(meet_var, time_var + durations[i_node] <= avail_end[i_node]))
    
    # Constraint for Carol (node7): exactly one incoming edge
    #   In next_var: destination node7 is column 6 (j=6)
    incoming_carol = [ next_var[i][6] for i in range(7) ]
    s.add(Sum([If(x, 1, 0) for x in incoming_carol]) == 1)
    
    # Travel time constraints for every possible edge in next_var
    for i in range(7):  # i: source node index (0 to 6)
        for j in range(7): # j: destination column (0 to 6: meaning node1 to node7)
            # Source node: 
            #   if i==0 -> node0 (start)
            #   if i>=1 -> node i (non-Carol meeting node)
            # Destination node: j+1 (node1 to node7)
            travel_time = travel_matrix[i][j+1]
            # If the edge is taken
            if i == 0:
                # Source is start (node0): leave at time0 (0), arrive at destination at time >= travel_time
                s.add(Implies(next_var[i][j], time[j] >= travel_time))
            else:
                # Source is node i (non-Carol meeting): leave at time[i-1] + duration[i]
                #   duration for node i is durations[i]
                s.add(Implies(next_var[i][j], 
                             time[j] >= time[i-1] + durations[i] + travel_time))
    
    # Objective: maximize the number of meetings (non-Carol) plus Carol (fixed)
    obj = Sum([If(meet[i], 1, 0) for i in range(6)])
    s.maximize(obj)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        # Reconstruct the path to get the order of meetings
        current = 0  # start at node0
        path = []
        # We'll traverse until we reach Carol (node7)
        #   next_var: if we are at node i, then look for j in [0,6] such that next_var[i][j] is true -> then next node is j+1
        while current != 7:
            found = False
            for j in range(7):
                if is_true(model[next_var[current][j]]):
                    next_node = j+1
                    path.append(next_node)
                    current = next_node
                    found = True
                    break
            if not found:
                break
        
        # Now, collect the meetings we did (non-Carol and Carol) in the path
        itinerary = []
        # Convert minutes to time string (from 9:00AM base)
        for node in path:
            if node == 7:  # Carol
                start_minutes = 750
                end_minutes = start_minutes + durations[7]
                start_hour = 9 + start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = 9 + end_minutes // 60
                end_minute = end_minutes % 60
                start_str = f"{int(start_hour):02d}:{int(start_minute):02d}"
                end_str = f"{int(end_hour):02d}:{int(end_minute):02d}"
                itinerary.append({"action": "meet", "person": "Carol", "start_time": start_str, "end_time": end_str})
            else:
                # Non-Carol meeting: node index (1 to 6)
                # The time variable for this node is time[node-1]
                time_var = time[node-1]
                start_minutes = model[time_var].as_long() if isinstance(model[time_var], z3.IntNumRef) else int(str(model.evaluate(time_var, model_completion=True)))
                duration_val = durations[node]
                end_minutes = start_minutes + duration_val
                start_hour = 9 + start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = 9 + end_minutes // 60
                end_minute = end_minutes % 60
                start_str = f"{int(start_hour):02d}:{int(start_minute):02d}"
                end_str = f"{int(end_hour):02d}:{int(end_minute):02d}"
                # Map node to person
                person_map = {
                    1: "Karen",
                    2: "Deborah",
                    3: "Elizabeth",
                    4: "Laura",
                    5: "Jason",
                    6: "Steven"
                }
                itinerary.append({"action": "meet", "person": person_map[node], "start_time": start_str, "end_time": end_str})
        
        # Output the itinerary in JSON format
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()