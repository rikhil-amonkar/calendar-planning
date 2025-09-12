from z3 import *
import json

# Define friend data
friends = [
    # Nancy
    {'name': 'Nancy', 'available_start': 480, 'available_end': 690, 'duration': 90, 'location': 4},
    # Lisa
    {'name': 'Lisa', 'available_start': 540, 'available_end': 990, 'duration': 45, 'location': 2},
    # Andrew
    {'name': 'Andrew', 'available_start': 690, 'available_end': 1215, 'duration': 60, 'location': 5},
    # Joshua
    {'name': 'Joshua', 'available_start': 720, 'available_end': 915, 'duration': 15, 'location': 3},
    # Kenneth
    {'name': 'Kenneth', 'available_start': 1275, 'available_end': 1320, 'duration': 30, 'location': 1},
    # John
    {'name': 'John', 'available_start': 1005, 'available_end': 1290, 'duration': 75, 'location': 6}
]

# Travel time matrix
travel_time_matrix = [
    [0, 21, 10, 5, 11, 10, 21],  # Embarcadero
    [19, 0, 21, 22, 10, 17, 26],  # Richmond
    [11, 20, 0, 9, 15, 9, 15],    # Union
    [4, 21, 9, 0, 13, 8, 19],     # Financial
    [10, 12, 12, 13, 0, 8, 22],   # Pacific
    [9, 14, 7, 9, 8, 0, 19],      # Nob
    [19, 25, 17, 19, 23, 20, 0]   # Bayview
]

# Create solver
solver = Optimize()

# Variables for each step
meet_vars = []
person_vars = []
start_vars = []
end_vars = [Int(f'end_{i}') for i in range(6)]
loc_vars = [Int(f'loc_{i}') for i in range(6)]

for step in range(6):
    meet = Bool(f'meet_{step}')
    person = Int(f'person_{step}')
    start = Int(f'start_{step}')
    meet_vars.append(meet)
    person_vars.append(person)
    start_vars.append(start)
    end = end_vars[step]
    loc = loc_vars[step]

    # Determine previous end and loc based on step
    if step == 0:
        prev_end = 540  # Starting at 9:00 AM
        prev_loc = 0    # Embarcadero
    else:
        prev_end = end_vars[step-1]
        prev_loc = loc_vars[step-1]

    # If meet is true, person must be between 0 and 5
    solver.add(Implies(meet, And(person >= 0, person <= 5)))

    # For each possible person, add constraints
    for p in range(6):
        p_loc = friends[p]['location']
        p_start = friends[p]['available_start']
        p_end_time = friends[p]['available_end']
        p_duration = friends[p]['duration']
        travel_time = travel_time_matrix[prev_loc][p_loc]

        solver.add(Implies(And(meet, person == p), start >= prev_end + travel_time))
        solver.add(Implies(And(meet, person == p), start >= p_start))
        solver.add(Implies(And(meet, person == p), start + p_duration <= p_end_time))
        solver.add(Implies(And(meet, person == p), end == start + p_duration))
        solver.add(Implies(And(meet, person == p), loc == p_loc))

    # If not meet, then end is prev_end and loc is prev_loc
    solver.add(Implies(Not(meet), end == prev_end))
    solver.add(Implies(Not(meet), loc == prev_loc))

# Maximize the number of meetings
solver.maximize(Sum([If(m, 1, 0) for m in meet_vars]))

# Check if the problem is satisfiable
result = solver.check()
if result == sat:
    model = solver.model()
    itinerary = []
    for i in range(6):
        meet = model.eval(meet_vars[i])
        if is_true(meet):
            person = model.eval(person_vars[i])
            start = model.eval(start_vars[i])
            p = person.as_long()
            friend = friends[p]
            name = friend['name']
            location = friend['location']
            location_names = [
                'Embarcadero', 'Richmond District', 'Union Square',
                'Financial District', 'Pacific Heights', 'Nob Hill', 'Bayview'
            ]
            location_name = location_names[location]
            duration = friend['duration']
            end_time = model.eval(end_vars[i]).as_long()
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            start_time_str = to_time_str(start.as_long())
            end_time_str = to_time_str(end_time)
            itinerary.append({
                "action": "meet",
                "location": location_name,
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")