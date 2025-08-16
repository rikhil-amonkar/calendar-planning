from z3 import *
import json

# Define friends and their data
friends = ['Laura', 'Brian', 'Karen', 'Stephanie', 'Helen', 'Sandra', 'Mary', 'Deborah', 'Elizabeth']
data = {
    'Laura': {'location': 'Alamo Square', 'availability': (14*60+30, 16*60+15), 'duration': 75},
    'Brian': {'location': 'Presidio', 'availability': (10*60+15, 17*60+0), 'duration': 30},
    'Karen': {'location': 'Russian Hill', 'availability': (18*60+0, 20*60+15), 'duration': 90},
    'Stephanie': {'location': 'North Beach', 'availability': (10*60+15, 16*60+0), 'duration': 75},
    'Helen': {'location': 'Golden Gate Park', 'availability': (11*60+30, 21*60+45), 'duration': 120},
    'Sandra': {'location': 'Richmond District', 'availability': (8*60+0, 15*60+15), 'duration': 30},
    'Mary': {'location': 'Embarcadero', 'availability': (16*60+45, 18*60+45), 'duration': 120},
    'Deborah': {'location': 'Financial District', 'availability': (19*60+0, 20*60+45), 'duration': 105},
    'Elizabeth': {'location': 'Marina District', 'availability': (8*60+30, 13*60+15), 'duration': 105},
}

# Define travel times between locations
travel_times = {
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Marina District'): 9,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
}

# Create Z3 solver
solver = Optimize()

# Create variables for each friend
met = {}  # boolean: whether the friend is met
start = {}  # integer: start time in minutes since midnight
end = {}  # integer: end time in minutes since midnight
is_first = {}  # boolean: whether this friend is the first in the itinerary

for name in friends:
    met[name] = Bool(f'met_{name}')
    start[name] = Int(f'start_{name}')
    end[name] = Int(f'end_{name}')
    is_first[name] = Bool(f'is_first_{name}')

# Add constraints for each friend
for name in friends:
    d = data[name]
    loc = d['location']
    avail_start, avail_end = d['availability']
    duration = d['duration']
    # If met, then start and end are within availability and duration
    solver.add(Implies(met[name], start[name] >= avail_start))
    solver.add(Implies(met[name], end[name] <= avail_end))
    solver.add(Implies(met[name], end[name] == start[name] + duration))
    # Ensure is_first implies met
    solver.add(Implies(is_first[name], met[name]))

# First meeting constraints
start_time_mission = 9 * 60  # 9:00 AM in minutes
M = 1440  # large enough constant to represent a full day in minutes

for name in friends:
    d = data[name]
    loc = d['location']
    travel_time = travel_times[('Mission District', loc)]
    # If the friend is met and is the first, then start >= 9:00 AM + travel time
    solver.add(Implies(And(met[name], is_first[name]), start[name] >= start_time_mission + travel_time))

# Ensure exactly one is_first among met friends
# Add constraints to prevent two friends from being first
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        p = friends[i]
        q = friends[j]
        solver.add(Not(And(met[p], is_first[p], met[q], is_first[q])))

# Add constraint that if any friend is met, then at least one is_first is true
solver.add(Or([And(met[name], is_first[name]) for name in friends]))

# Add constraints for travel times between pairs of friends
for i in range(len(friends)):
    for j in range(len(friends)):
        if i == j:
            continue
        p = friends[i]
        q = friends[j]
        loc_p = data[p]['location']
        loc_q = data[q]['location']
        travel_time_pq = travel_times[(loc_p, loc_q)]
        travel_time_qp = travel_times[(loc_q, loc_p)]
        # If both are met, then either p is before q or q is before p
        solver.add(Implies(And(met[p], met[q]), Or(
            start[q] >= end[p] + travel_time_pq,
            start[p] >= end[q] + travel_time_qp
        )))

# Maximize the number of friends met
solver.maximize(Sum([If(met[name], 1, 0) for name in friends]))

# Solve
if solver.check() == sat:
    model = solver.model()
    result = []
    for name in friends:
        if is_true(model.eval(met[name])):
            s = model.eval(start[name]).as_long()
            e = model.eval(end[name]).as_long()
            def to_time(m):
                h = m // 60
                m = m % 60
                return f"{h:02d}:{m:02d}"
            start_time = to_time(s)
            end_time = to_time(e)
            result.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    # Sort by start time
    result.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": result}))
else:
    print("No solution found.")