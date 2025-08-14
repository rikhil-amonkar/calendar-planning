from z3 import *

# Define the locations
locations = ["Pacific Heights", "Nob Hill", "Russian Hill", "The Castro", "Sunset District", "Haight-Ashbury"]

# Define the travel times between locations
travel_times = {
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 25,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Sunset District"): 15,
}

# Define the constraints for meeting friends
meetings = {
    "Ronald": {"location": "Nob Hill", "start": 10*60, "end": 17*60, "min_duration": 105},
    "Sarah": {"location": "Russian Hill", "start": 7*60 + 15, "end": 9*60 + 30, "min_duration": 45},
    "Helen": {"location": "The Castro", "start": 13*60 + 30, "end": 17*60, "min_duration": 120},
    "Joshua": {"location": "Sunset District", "start": 14*60 + 15, "end": 19*60 + 30, "min_duration": 90},
    "Margaret": {"location": "Haight-Ashbury", "start": 10*60 + 15, "end": 22*60, "min_duration": 60},
}

# Create a solver instance
solver = Solver()

# Define the time variables for each location visit
visit_times = {loc: Int(f"visit_time_{loc}") for loc in locations}

# Add constraints for the initial visit time
solver.add(visit_times["Pacific Heights"] == 9*60)

# Add constraints for travel times and meeting durations
for friend, details in meetings.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Constraint to ensure we arrive at the location within the friend's availability
    solver.add(visit_times[loc] >= start)
    solver.add(visit_times[loc] + min_duration <= end)
    
    # Ensure we have enough time to travel to the next location
    for next_loc in locations:
        if next_loc != loc:
            travel_time = travel_times[(loc, next_loc)]
            solver.add(visit_times[next_loc] >= visit_times[loc] + min_duration + travel_time)

# Optimize to maximize the number of friends met
# Since Z3 does not have a built-in maximize function, we use a trick to find the optimal solution
objective = Int("objective")
solver.add(objective == Sum([If(And(visit_times[details["location"]] >= details["start"], 
                                    visit_times[details["location"]] + details["min_duration"] <= details["end"]), 
                             1, 0) for friend, details in meetings.items()]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        print(f"Visit {loc} at {model[visit_times[loc]] / 60} hours")
else:
    print("No solution found")