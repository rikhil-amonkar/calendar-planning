from z3 import *

# Define the locations
locations = ["Bayview", "Nob Hill", "Union Square", "Chinatown", "The Castro", "Presidio", "Pacific Heights", "Russian Hill"]

# Define the travel times
travel_times = {
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "The Castro"): 20,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Russian Hill"): 14,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Pacific Heights"): 7,
}

# Define the meeting constraints
meetings = {
    "Paul": {"location": "Nob Hill", "start": 16.25, "end": 21.25, "min_duration": 1},
    "Carol": {"location": "Union Square", "start": 18.0, "end": 20.25, "min_duration": 2},
    "Patricia": {"location": "Chinatown", "start": 20.0, "end": 21.5, "min_duration": 1.25},
    "Karen": {"location": "The Castro", "start": 17.0, "end": 19.0, "min_duration": 0.75},
    "Nancy": {"location": "Presidio", "start": 11.75, "end": 22.0, "min_duration": 0.5},
    "Jeffrey": {"location": "Pacific Heights", "start": 20.0, "end": 20.75, "min_duration": 0.75},
    "Matthew": {"location": "Russian Hill", "start": 15.75, "end": 21.75, "min_duration": 1.25},
}

# Create a solver instance
solver = Solver()

# Define the variables for each meeting
meeting_vars = {}
for name, details in meetings.items():
    start_var = Real(f"{name}_start")
    end_var = Real(f"{name}_end")
    meeting_vars[name] = (start_var, end_var)
    solver.add(start_var >= details["start"])
    solver.add(end_var <= details["end"])
    solver.add(end_var - start_var >= details["min_duration"])

# Define the sequence of visits
num_meetings = 5
visit_order = [String(f"visit_{i}") for i in range(num_meetings)]

# Initial location at 9:00 AM
initial_location = "Bayview"
solver.add(visit_order[0] == initial_location)

# Define the travel constraints
previous_time = Real("start_time")
solver.add(previous_time == 9.0)

# Define the selected meetings
selected_meetings = BoolVector("selected_meeting", len(meetings))
selected_meetings_map = {name: selected_meetings[i] for i, name in enumerate(meetings)}

# Ensure exactly 5 meetings are selected
solver.add(Sum(selected_meetings) == num_meetings)

# Add constraints for each meeting
for i in range(num_meetings):
    name = None
    for candidate_name, details in meetings.items():
        if details["location"] == visit_order[i].as_string():
            name = candidate_name
            break
    if name is None:
        continue
    
    start_var, end_var = meeting_vars[name]
    travel_time = travel_times[(visit_order[i-1].as_string(), visit_order[i].as_string())] if i > 0 else 0
    solver.add(start_var >= previous_time + travel_time / 60.0)
    previous_time = end_var
    solver.add(selected_meetings_map[name])

# Ensure all visits are unique
solver.add(Distinct(visit_order))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for i in range(num_meetings):
        location = model[visit_order[i]].as_string()
        for name, details in meetings.items():
            if details["location"] == location:
                start_var, end_var = meeting_vars[name]
                start_time = model[start_var].as_decimal(3)
                end_time = model[end_var].as_decimal(3)
                print(f"Meet {name} at {location} from {start_time} to {end_time}")
else:
    print("No solution found.")