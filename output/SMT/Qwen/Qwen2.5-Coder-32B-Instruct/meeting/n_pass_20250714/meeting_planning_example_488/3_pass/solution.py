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

# Binary variables to indicate whether we meet each friend
meet_vars = {friend: Bool(f"meet_{friend}") for friend in meetings}

# Constraints to ensure we meet each friend only if we visit their location within their availability
for friend, details in meetings.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Constraint to ensure we arrive at the location within the friend's availability
    solver.add(Implies(meet_vars[friend], And(visit_times[loc] >= start, visit_times[loc] + min_duration <= end)))
    
    # Ensure we have enough time to travel to the next location if we meet this friend
    for next_loc in locations:
        if next_loc != loc:
            travel_time = travel_times[(loc, next_loc)]
            solver.add(Implies(meet_vars[friend], visit_times[next_loc] >= visit_times[loc] + min_duration + travel_time))

# Constraint to ensure we meet exactly 4 friends
solver.add(Sum([If(meet_vars[friend], 1, 0) for friend in meetings]) == 4)

# Optimize to minimize the total travel time
# Since Z3 does not have a built-in minimize function, we use a trick to find the optimal solution
total_travel_time = Int("total_travel_time")
solver.add(total_travel_time == Sum([If(meet_vars[friend], 
                                      travel_times[(locations[0], meetings[friend]["location"])] +
                                      meetings[friend]["min_duration"] +
                                      travel_times[(meetings[friend]["location"], locations[0])],
                                      0) for friend in meetings]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        print(f"Visit {loc} at {model[visit_times[loc]] / 60} hours")
    for friend, var in meet_vars.items():
        if model[var]:
            details = meetings[friend]
            print(f"Meet {friend} at {model[visit_times[details['location']]] / 60} hours for {details['min_duration']} minutes")
else:
    print("No solution found")