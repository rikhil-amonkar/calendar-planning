from z3 import *

# Define friends and their data
friends = [
    {
        'name': 'Sarah',
        'location': 'Sunset',
        'available_start': 645,  # 10:45 AM
        'available_end': 1140,   # 7:00 PM
        'duration': 30
    },
    {
        'name': 'Richard',
        'location': 'Haight-Ashbury',
        'available_start': 705,  # 11:45 AM
        'available_end': 945,    # 3:45 PM
        'duration': 90
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission',
        'available_start': 660,  # 11:00 AM
        'available_end': 1035,   # 5:15 PM
        'duration': 120
    },
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'available_start': 1035, # 6:15 PM
        'available_end': 1245,   # 8:45 PM
        'duration': 90
    }
]

# Define travel times between locations
travel_time = {
    ('Richmond', 'Sunset'): 11,
    ('Richmond', 'Haight-Ashbury'): 10,
    ('Richmond', 'Mission'): 20,
    ('Richmond', 'Golden Gate Park'): 9,
    ('Sunset', 'Richmond'): 12,
    ('Sunset', 'Haight-Ashbury'): 15,
    ('Sunset', 'Mission'): 24,
    ('Sunset', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond'): 10,
    ('Haight-Ashbury', 'Sunset'): 15,
    ('Haight-Ashbury', 'Mission'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission', 'Richmond'): 20,
    ('Mission', 'Sunset'): 24,
    ('Mission', 'Haight-Ashbury'): 12,
    ('Mission', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond'): 7,
    ('Golden Gate Park', 'Sunset'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission'): 17,
}

# Create solver
solver = Optimize()

# Create variables for each friend
include_vars = []
start_vars = []
end_vars = []
index_vars = []

for friend in friends:
    name = friend['name']
    include = Bool(f'include_{name}')
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    index = Int(f'index_{name}')
    include_vars.append(include)
    start_vars.append(start)
    end_vars.append(end)
    index_vars.append(index)

# Add constraints for each friend
for i, friend in enumerate(friends):
    name = friend['name']
    include = include_vars[i]
    start = start_vars[i]
    end = end_vars[i]
    index = index_vars[i]
    loc = friend['location']
    duration = friend['duration']
    available_start = friend['available_start']
    available_end = friend['available_end']

    # If included, end = start + duration
    solver.add(Implies(include, end == start + duration))
    # If included, start >= available_start
    solver.add(Implies(include, start >= available_start))
    # If included, end <= available_end
    solver.add(Implies(include, end <= available_end))

    # Constraint for being the first in the sequence (arrival from Richmond)
    is_first = True
    for j, other in enumerate(friends):
        if i == j:
            continue
        other_include = include_vars[j]
        other_index = index_vars[j]
        is_first = And(is_first, Implies(other_include, other_index >= index))
    solver.add(Implies(And(include, is_first), start >= 540 + travel_time[('Richmond', loc)]))

# Add constraints between pairs of friends
for i, friendA in enumerate(friends):
    for j, friendB in enumerate(friends):
        if i == j:
            continue
        includeA = include_vars[i]
        includeB = include_vars[j]
        indexA = index_vars[i]
        indexB = index_vars[j]
        locA = friendA['location']
        locB = friendB['location']
        solver.add(Implies(And(includeA, includeB, indexA < indexB), end_vars[i] + travel_time[(locA, locB)] <= start_vars[j]))

# Ensure that indices are unique for included friends
for i in range(len(friends)):
    for j in range(len(friends)):
        if i != j:
            include_i = include_vars[i]
            include_j = include_vars[j]
            index_i = index_vars[i]
            index_j = index_vars[j]
            solver.add(Implies(And(include_i, include_j), index_i != index_j))

# Maximize the number of friends included
objective = Sum([If(include, 1, 0) for include in include_vars])
solver.maximize(objective)

# Check for solution
result = solver.check()
if result == sat:
    model = solver.model()
    included = []
    for i, friend in enumerate(friends):
        name = friend['name']
        include = model.evaluate(include_vars[i])
        if is_true(include):
            included.append({
                'name': name,
                'start': model.evaluate(start_vars[i]),
                'end': model.evaluate(end_vars[i]),
                'index': model.evaluate(index_vars[i])
            })
    included.sort(key=lambda x: x['index'])
    itinerary = []
    for entry in included:
        name = entry['name']
        start_time = entry['start']
        end_time = entry['end']
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")