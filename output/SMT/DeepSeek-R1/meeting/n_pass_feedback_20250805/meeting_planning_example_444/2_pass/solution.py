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

# Variables
y = {i: Bool(f"y_{i}") for i in meetings}  # Whether we meet friend i
x0 = {i: Bool(f"x0_{i}") for i in meetings}  # Edge from start to meeting i
x = {(i, j): Bool(f"x_{i}_{j}") for i in meetings for j in meetings if i != j}  # Edges between meetings
x6 = {i: Bool(f"x6_{i}") for i in meetings}  # Edge from meeting i to sink
u = {i: Real(f"u_{i}") for i in meetings}  # Start time of meeting i (in minutes)

# Flow conservation for meetings
for i in meetings:
    # Inflow: from start or from another meeting
    inflow_conditions = [x0[i]]
    for j in meetings:
        if j != i:
            inflow_conditions.append(x[(j, i)])
    s.add(y[i] == Or(inflow_conditions))
    
    # Outflow: to sink or to another meeting
    outflow_conditions = [x6[i]]
    for j in meetings:
        if j != i:
            outflow_conditions.append(x[(i, j)])
    s.add(y[i] == Or(outflow_conditions))

# Flow conservation for start and sink: outflow from start equals inflow to sink
s.add(Sum([If(x0[i], 1, 0) for i in meetings]) == Sum([If(x6[i], 1, 0) for i in meetings]))
# At most one edge from start
s.add(Sum([If(x0[i], 1, 0) for i in meetings]) <= 1)

# Time constraints for meetings
for i in meetings:
    s.add(Implies(y[i], 
                  And(u[i] >= available_start[i],
                      u[i] + min_duration[i] <= available_end[i])))

# Travel time constraints for edges from start to meeting i
for i in meetings:
    tt = travel_times[("Financial District", loc[i])]
    s.add(Implies(x0[i], u[i] >= 540 + tt))  # 540 minutes = 9:00 AM

# Travel time constraints for edges between meetings
for i in meetings:
    for j in meetings:
        if i != j:
            tt = travel_times[(loc[i], loc[j])]
            s.add(Implies(x[(i, j)], 
                          u[j] >= u[i] + min_duration[i] + tt))

# Objective: maximize the number of meetings
total_meetings = Sum([If(y[i], 1, 0) for i in meetings])
s.maximize(total_meetings)

# Solve and get the solution
if s.check() == sat:
    m = s.model()
    visited_meetings = []
    for i in meetings:
        if is_true(m[y[i]]):
            start_val = m[u[i]]
            # Convert Z3 value to integer
            if is_int_value(start_val):
                start_minutes = start_val.as_long()
            else:
                # For real values, we get a string representation and convert
                start_str_val = str(start_val)
                if '/' in start_str_val:
                    # It's a fraction
                    num, den = start_str_val.split('/')
                    start_minutes = int(float(num) / float(den))
                else:
                    start_minutes = int(float(start_str_val))
            end_minutes = start_minutes + min_duration[i]
            start_str = f"{start_minutes//60:02d}:{start_minutes%60:02d}"
            end_str = f"{end_minutes//60:02d}:{end_minutes%60:02d}"
            visited_meetings.append((start_minutes, index_to_name[i], start_str, end_str))
    visited_meetings.sort(key=lambda x: x[0])
    itinerary_list = []
    for (start_minutes, person, start_str, end_str) in visited_meetings:
        itinerary_list.append({
            "action": "meet",
            "person": person,
            "start_time": start_str,
            "end_time": end_str
        })
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary_list}))
else:
    print('SOLUTION:')
    print(json.dumps({"itinerary": []}))