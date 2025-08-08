from z3 import *
import json

# Define locations
locations = [
    "Richmond District",      # node0
    "The Castro",             # node1 (Matthew)
    "Nob Hill",               # node2 (Rebecca)
    "Marina District",        # node3 (Brian)
    "Pacific Heights",        # node4 (Emily)
    "Haight-Ashbury",         # node5 (Karen)
    "Mission District",       # node6 (Stephanie)
    "Chinatown",              # node7 (James)
    "Russian Hill",           # node8 (Steven)
    "Alamo Square",           # node9 (Elizabeth)
    "Bayview"                 # node10 (William)
]

# Travel time dictionary
travel_dict = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,

    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,

    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,

    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,

    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,

    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,

    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,

    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,

    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,

    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,

    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16
}

# Create 11x11 travel matrix
travel_matrix = [[0]*11 for _ in range(11)]
for i in range(11):
    for j in range(11):
        from_loc = locations[i]
        to_loc = locations[j]
        travel_matrix[i][j] = travel_dict.get((from_loc, to_loc), 0)

# Available times in minutes from midnight
available_start = {
    1: 16*60+30,   # Matthew: 16:30
    2: 15*60+15,   # Rebecca: 15:15
    3: 14*60+15,   # Brian: 14:15
    4: 11*60+15,   # Emily: 11:15
    5: 11*60+45,   # Karen: 11:45
    6: 13*60,      # Stephanie: 13:00
    7: 14*60+30,   # James: 14:30
    8: 14*60,      # Steven: 14:00
    9: 13*60,      # Elizabeth: 13:00
    10: 18*60+15   # William: 18:15
}

available_end = {
    1: 20*60,      # 20:00
    2: 19*60+15,   # 19:15
    3: 22*60,      # 22:00
    4: 19*60+45,   # 19:45
    5: 17*60+30,   # 17:30
    6: 15*60+45,   # 15:45
    7: 19*60,      # 19:00
    8: 20*60,      # 20:00
    9: 17*60+15,   # 17:15
    10: 20*60+15   # 20:15
}

min_duration = {
    1: 45,     # Matthew
    2: 105,    # Rebecca
    3: 30,     # Brian
    4: 15,     # Emily
    5: 30,     # Karen
    6: 75,     # Stephanie
    7: 120,    # James
    8: 30,     # Steven
    9: 120,    # Elizabeth
    10: 90     # William
}

# Mapping of node index to friend name
friends = {
    1: "Matthew",
    2: "Rebecca",
    3: "Brian",
    4: "Emily",
    5: "Karen",
    6: "Stephanie",
    7: "James",
    8: "Steven",
    9: "Elizabeth",
    10: "William"
}

# Initialize Z3 solver
s = Solver()

# x[i][j]: Boolean variable for traveling from node i to node j
# i in [0,10] (0=start, 1-10=meetings), j in [1,11] (1-10=meetings, 11=end)
x = [[Bool(f'x_{i}_{j}') for j in range(11)] for i in range(11)]

# Time variables for meetings (j=1 to 10)
a = [Int(f'a_{j}') for j in range(1, 11)]        # Arrival time at meeting j
start_time = [Int(f'start_{j}') for j in range(1, 11)]  # Start time of meeting j
end_time = [Int(f'end_{j}') for j in range(1, 11)]      # End time of meeting j

# Start node leaves at 9:00 AM (540 minutes)
e0 = 540

# Flow constraints
# 1. Exactly one outgoing edge from start (node0)
s.add(Sum([If(x[0][j], 1, 0) for j in range(11)]) == 1)

# 2. Exactly one incoming edge to end (represented by j=10, since x[i][10] corresponds to end node)
s.add(Sum([If(x[i][10], 1, 0) for i in range(11)]) == 1)

# 3. For each meeting node j (1-10): 
#    - If visited, exactly one incoming and one outgoing edge
#    - If not visited, no incoming or outgoing edges
for j in range(1, 11):  # j: meeting node index (1-10)
    # Incoming edges: from any node i to meeting j (x[i][j-1] because j-1 is the index in x for meeting j)
    incoming = Sum([If(x[i][j-1], 1, 0) for i in range(11)])
    # Outgoing edges: from meeting j to any node k (x[j][k] for k in 0..10, but note: j is the meeting node index 1..10 -> stored at x[j]? Actually, x is indexed [i][j] for i in 0..10 and j in 0..10. For meeting node j (which is at index j in 1..10), we use x[j] for outgoing? But our x is defined for nodes 0..10 (11 nodes) and the end node is j=10 in the x list? Actually, our x[i] has 11 elements: for j in 0..10, meaning:
    #   j=0: meeting1
    #   j=1: meeting2
    #   ...
    #   j=9: meeting10
    #   j=10: end
    # So for meeting node j (j in 1..10), its outgoing edges are in x[j][k] for k in range(0,11) (but note: j is the node index, so for node1 (Matthew) we use x[1]? But our x is defined for i in 0..10. So we need to use the node index to access x? 
    # We have:
    #   x[i][j]: i is the from node (0..10), j is the to node index in the list: j=0..10 correspond to meetings 1..10 and end (j=10).
    # For outgoing from meeting node j (node index j, which is 1..10), we look at x[j][k] for k in 0..10 (which are the outgoing edges to meetings 1..10 and end).
    outgoing = Sum([If(x[j][k], 1, 0) for k in range(11)])
    # meet_j is true if there is exactly one incoming edge
    meet_j = (incoming == 1)
    # Constraints: if meet_j, then outgoing must be 1; if not, then outgoing must be 0.
    s.add(meet_j == (outgoing == 1))

# 4. Time constraints for meetings
for j in range(1, 11):  # j: meeting node index (1-10)
    # meet_j: defined as (sum of incoming edges to j is 1)
    meet_j = (Sum([If(x[i][j-1], 1, 0) for i in range(11)]) == 1)
    
    # a[j-1]: arrival time at meeting j
    # a[j-1] = sum over i: If x[i][j-1] is true, then (e0 if i==0 else end_time[i-1]) + travel_time[i][j], else 0
    terms = []
    for i in range(0, 11):
        # If coming from start (i=0)
        if i == 0:
            # Travel time from node0 (start) to node j (which is travel_matrix[0][j] because j is the node index j)
            terms.append(If(x[i][j-1], e0 + travel_matrix[0][j], 0))
        else:
            # Travel time from meeting node i (node index i) to meeting node j (node index j): travel_matrix[i][j]
            terms.append(If(x[i][j-1], end_time[i-1] + travel_matrix[i][j], 0))
    s.add(a[j-1] == Sum(terms))
    
    # Time constraints for meeting j
    s.add(start_time[j-1] >= a[j-1])
    s.add(Implies(meet_j, start_time[j-1] >= available_start[j]))
    s.add(end_time[j-1] == start_time[j-1] + min_duration[j])
    s.add(Implies(meet_j, end_time[j-1] <= available_end[j]))

# 5. No self loops is inherent

# Objective: maximize number of meetings
total_meetings = Sum([If(Sum([If(x[i][j-1], 1, 0) for i in range(11)]) == 1, 1, 0) for j in range(1,11)])
s.maximize(total_meetings)

# Solve
if s.check() == sat:
    model = s.model()
    # Extract the path
    path = []
    current = 0  # start at node0
    while current != 11:  # until we reach the end node
        found = False
        for j in range(11):  # j: index in the x[current] list: j=0..9 -> meetings 1..10, j=10 -> end
            if is_true(model[x[current][j]]):
                if j == 10:  # end node
                    current = 11
                    found = True
                    break
                else:
                    next_node = j + 1  # because j=0 -> meeting1 (node1), j=1->meeting2 (node2), etc.
                    path.append(next_node)
                    current = next_node
                    found = True
                    break
        if not found:
            break
    
    # Create itinerary
    itinerary = []
    for node in path:
        j = node  # node index: 1..10
        # Get the start and end times
        start_val = model[start_time[j-1]].as_long()
        end_val = model[end_time[j-1]].as_long()
        # Convert to HH:MM
        def min_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        start_str = min_to_time(start_val)
        end_str = min_to_time(end_val)
        person = friends[j]
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": start_str,
            "end_time": end_str
        })
    
    # Output
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")