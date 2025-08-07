from z3 import *
import json

# Define meetings and their properties
meetings = [1, 2, 3, 4, 5]
index_to_name = {
    1: "Ronald",
    2: "Patricia",
    3: "Laura",
    4: "Emily",
    5: "Mary"
}

loc = {
    1: "Russian Hill",
    2: "Sunset District",
    3: "North Beach",
    4: "The Castro",
    5: "Golden Gate Park"
}

available_start = {
    1: 13*60 + 45,  # 13:45
    2: 9*60 + 15,    # 09:15
    3: 12*60 + 30,   # 12:30
    4: 16*60 + 15,   # 16:15
    5: 15*60         # 15:00
}

available_end = {
    1: 17*60 + 15,  # 17:15
    2: 22*60,        # 22:00
    3: 12*60 + 45,   # 12:45
    4: 18*60 + 30,   # 18:30
    5: 16*60 + 30    # 16:30
}

min_duration = {
    1: 105,  # 105 minutes
    2: 60,   # 60 minutes
    3: 15,   # 15 minutes
    4: 60,   # 60 minutes
    5: 60    # 60 minutes
}

# Travel times dictionary
travel_times = {
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13
}

# Create solver
s = Optimize()

# Define special nodes
start_node = 0
sink_node = 6

# Variables
y = {i: Bool(f"y_{i}") for i in meetings}  # Whether meeting i is visited
x = {}  # Edges: (from, to)
# Possible edges: start -> meetings, meetings -> meetings, meetings -> sink
for i in [start_node] + meetings:
    for j in meetings + [sink_node]:
        if i != j:
            x[(i, j)] = Bool(f"x_{i}_{j}")

u = {i: Real(f"u_{i}") for i in meetings}  # Start time of meeting i

# Constraints

# Start node: exactly one outgoing edge
s.add(Sum([If(x[(start_node, j)], 1, 0) for j in meetings + [sink_node]]) == 1)

# Sink node: exactly one incoming edge
s.add(Sum([If(x[(i, sink_node)], 1, 0) for i in [start_node] + meetings]) == 1)

# Meeting nodes: flow conservation
for i in meetings:
    # Inflow: from start or other meetings
    inflow = Sum([If(x[(j, i)], 1, 0) for j in [start_node] + meetings if j != i])
    # Outflow: to sink or other meetings
    outflow = Sum([If(x[(i, j)], 1, 0) for j in meetings + [sink_node] if j != i])
    s.add(y[i] == (inflow == 1))
    s.add(y[i] == (outflow == 1))

# Time window constraints
for i in meetings:
    s.add(Implies(y[i], 
                  And(u[i] >= available_start[i],
                      u[i] + min_duration[i] <= available_end[i])))

# Travel time constraints
for j in meetings:
    # From start to meeting j
    tt = travel_times[("Financial District", loc[j])]
    s.add(Implies(x[(start_node, j)], 
                  u[j] >= 540 + tt))  # 540 min = 9:00 AM

for i in meetings:
    for j in meetings:
        if i != j:
            tt = travel_times[(loc[i], loc[j])]
            s.add(Implies(x[(i, j)], 
                          u[j] >= u[i] + min_duration[i] + tt))

# Objective: maximize number of meetings
total_meetings = Sum([If(y[i], 1, 0) for i in meetings])
s.maximize(total_meetings)

# Solve and output
if s.check() == sat:
    m = s.model()
    # Reconstruct path
    path = []
    current = start_node
    while current != sink_node:
        # Find next node
        next_node = None
        for j in meetings + [sink_node]:
            if (current, j) in x and is_true(m[x[(current, j)]]):
                next_node = j
                break
        if next_node == sink_node:
            break
        path.append(next_node)
        current = next_node
    
    # Build itinerary in path order
    itinerary_list = []
    for node in path:
        if is_true(m[y[node]]):  # Should always be true for nodes in path
            # Get start time value
            start_val = m[u[node]]
            if is_int_value(start_val):
                start_minutes = start_val.as_long()
            else:
                # Handle rational values
                start_str = str(start_val)
                if '/' in start_str:
                    num, den = start_str.split('/')
                    start_minutes = int(float(num) / float(den))
                else:
                    start_minutes = int(float(start_str))
            
            end_minutes = start_minutes + min_duration[node]
            start_str = f"{start_minutes//60:02d}:{start_minutes%60:02d}"
            end_str = f"{end_minutes//60:02d}:{end_minutes%60:02d}"
            itinerary_list.append({
                "action": "meet",
                "person": index_to_name[node],
                "start_time": start_str,
                "end_time": end_str
            })
    
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary_list}))
else:
    print('SOLUTION:')
    print(json.dumps({"itinerary": []}))