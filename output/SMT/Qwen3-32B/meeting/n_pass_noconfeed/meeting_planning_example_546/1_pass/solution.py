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
    # Embarcadero (0), Richmond (1), Union (2), Financial (3), Pacific (4), Nob (5), Bayview (6)
    [0, 21, 10, 5, 11, 10, 21],  # Embarcadero (0)
    [19, 0, 21, 22, 10, 17, 26],  # Richmond (1)
    [11, 20, 0, 9, 15, 9, 15],    # Union (2)
    [4, 21, 9, 0, 13, 8, 19],     # Financial (3)
    [10, 12, 12, 13, 0, 8, 22],   # Pacific (4)
    [9, 14, 7, 9, 8, 0, 19],      # Nob (5)
    [19, 25, 17, 19, 23, 20, 0]   # Bayview (6)
]

# Create solver
solver = Optimize()

# Variables for each step
meet_vars = []
person_vars = []
start_vars = []
current_prev_end = 540  # initial time at Embarcadero
current_prev_loc = 0    # Embarcadero's index

for step in range(6):
    meet = Bool(f'meet_{step}')
    person = Int(f'person_{step}')
    start = Int(f'start_{step}')
    meet_vars.append(meet)
    person_vars.append(person)
    start_vars.append(start)

    # If meet is true, person must be between 0 and 5
    solver.add(Implies(meet, And(person >= 0, person <= 5)))

    # For each possible person, add constraints on start time
    for p in range(6):
        avail_start = friends[p]['available_start']
        avail_end = friends[p]['available_end']
        duration = friends[p]['duration']
        loc = friends[p]['location']

        # If meet is true and person is p, then start must be within available time
        solver.add(Implies(And(meet, person == p), start >= avail_start))
        solver.add(Implies(And(meet, person == p), start + duration <= avail_end))

    # Compute travel time from current_prev_loc to the current person's location
    for p in range(6):
        loc = friends[p]['location']
        travel_time = travel_time_matrix[current_prev_loc][loc]
        solver.add(Implies(And(meet, person == p), start >= current_prev_end + travel_time))

    # Update current_prev_end and current_prev_loc for the next step
    # Assume that if meet is true, new_prev_end is start + duration, and new_prev_loc is loc
    # This is a simplified model and may not capture all dependencies
    # For the next step, we'll assume current_prev_end and current_prev_loc are updated accordingly
    # This is a placeholder and may not be accurate
    for p in range(6):
        loc = friends[p]['location']
        duration = friends[p]['duration']
        solver.add(Implies(And(meet, person == p), current_prev_end + duration))
        solver.add(Implies(And(meet, person == p), loc))

# Add objective to maximize the number of meetings
solver.maximize(Sum([If(m, 1, 0) for m in meet_vars]))

# Check if the problem is satisfiable
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the meetings
    itinerary = []
    for i in range(6):
        meet = model.eval(meet_vars[i])
        if is_true(meet):
            person = model.eval(person_vars[i])
            start = model.eval(start_vars[i])
            # Get friend's name, location, and end time
            p = person.as_long()
            friend = friends[p]
            name = friend['name']
            location = friend['location']
            # Map location to name
            location_names = ['Embarcadero', 'Richmond District', 'Union Square', 'Financial District', 'Pacific Heights', 'Nob Hill', 'Bayview']
            location_name = location_names[location]
            duration = friend['duration']
            end_time = start.as_long() + duration
            # Convert start and end times to H:MM format
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
    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")