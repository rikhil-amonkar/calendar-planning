from z3 import *
import json

# Define travel times between locations
travel_dict = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Pacific Heights'): 16
}

# Define friends and their constraints
friends = [
    {"name": "William", "loc": "Alamo Square", "start": (15, 15), "end": (17, 15), "min_dur": 60},
    {"name": "Joshua", "loc": "Richmond District", "start": (7, 0), "end": (20, 0), "min_dur": 15},
    {"name": "Joseph", "loc": "Financial District", "start": (11, 15), "end": (13, 30), "min_dur": 15},
    {"name": "David", "loc": "Union Square", "start": (16, 45), "end": (19, 15), "min_dur": 45},
    {"name": "Brian", "loc": "Fisherman's Wharf", "start": (13, 45), "end": (20, 45), "min_dur": 105},
    {"name": "Karen", "loc": "Marina District", "start": (11, 30), "end": (18, 30), "min_dur": 15},
    {"name": "Anthony", "loc": "Haight-Ashbury", "start": (7, 15), "end": (10, 30), "min_dur": 30},
    {"name": "Matthew", "loc": "Mission District", "start": (17, 15), "end": (19, 15), "min_dur": 120},
    {"name": "Helen", "loc": "Pacific Heights", "start": (8, 0), "end": (12, 0), "min_dur": 75},
    {"name": "Jeffrey", "loc": "Golden Gate Park", "start": (19, 0), "end": (21, 30), "min_dur": 60}
]

# Initialize Z3 solver
solver = Solver()

# Number of meetings: 10 friends + 1 dummy
n = 11

# Dummy meeting (index 0)
m = [None] * n
s = [None] * n
d = [0] * n
locs = [None] * n

# Dummy meeting at The Castro at time 0
m[0] = True
s[0] = 0
d[0] = 0
locs[0] = "The Castro"

# Real meetings (indices 1 to 10)
for i in range(1, n):
    friend = friends[i-1]
    m[i] = Bool(f'm_{i}')
    s[i] = Int(f's_{i}')
    d[i] = friend["min_dur"]
    locs[i] = friend["loc"]

# Add constraints for each friend's availability
for i in range(1, n):
    friend = friends[i-1]
    start_minutes = friend["start"][0] * 60 + friend["start"][1] - 9 * 60
    end_minutes = friend["end"][0] * 60 + friend["end"][1] - 9 * 60
    solver.add(Implies(m[i], s[i] >= start_minutes))
    solver.add(Implies(m[i], s[i] + d[i] <= end_minutes))

# Add travel constraints for every pair of meetings (including dummy)
for i in range(n):
    for j in range(i + 1, n):
        # Skip if both are not met, but we use Implies
        time_ij = travel_dict.get((locs[i], locs[j]))
        time_ji = travel_dict.get((locs[j], locs[i]))
        if time_ij is None or time_ji is None:
            continue
        constraint = Implies(And(m[i], m[j]), Or(
            s[i] + d[i] + time_ij <= s[j],
            s[j] + d[j] + time_ji <= s[i]
        ))
        solver.add(constraint)

# Objective: maximize the number of meetings
obj = Sum([If(m[i], 1, 0) for i in range(1, n)])
solver.maximize(obj)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(1, n):
        if model.evaluate(m[i]):
            start_val = model.evaluate(s[i])
            if isinstance(start_val, IntNumRef):
                start_minutes = start_val.as_long()
                total_minutes = start_minutes + 9 * 60
                hour = total_minutes // 60
                minute = total_minutes % 60
                start_time = f"{hour:02d}:{minute:02d}"
                end_minutes_val = start_minutes + d[i] + 9 * 60
                end_hour = end_minutes_val // 60
                end_minute = end_minutes_val % 60
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i-1]["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
    # Sort itinerary by start_time
    itinerary.sort(key=lambda x: x["start_time"])
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")