from z3 import *

# Define the locations
locations = ["Russian Hill", "Nob Hill", "Mission District", "Embarcadero"]

# Define the travel times in minutes
travel_times = {
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Embarcadero"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Embarcadero"): 9,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20
}

# Define the friends' availability and meeting requirements
friends = {
    "Patricia": {"location": "Nob Hill", "start": 1830, "end": 2145, "min_meeting_time": 90},
    "Ashley": {"location": "Mission District", "start": 2030, "end": 2115, "min_meeting_time": 45},
    "Timothy": {"location": "Embarcadero", "start": 945, "end": 1745, "min_meeting_time": 120}
}

# Convert times to minutes since midnight for easier calculations
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a Z3 solver instance
solver = Solver()

# Define the variables for the start time at each location
start_times = {loc: Int(f"start_{loc}") for loc in locations}

# Add constraints for the initial start time at Russian Hill
solver.add(start_times["Russian Hill"] == 540)  # 9:00 AM in minutes

# Add constraints for the travel times between locations
for (loc1, loc2), travel_time in travel_times.items():
    solver.add(start_times[loc2] >= start_times[loc1] + travel_time)

# Add constraints for meeting each friend
for friend, details in friends.items():
    loc = details["location"]
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_meeting_time = details["min_meeting_time"]
    
    # Friend must be available when you arrive
    solver.add(start_times[loc] + min_meeting_time <= end)
    solver.add(start_times[loc] >= start)

# Objective: Maximize the number of friends met
# Since we have specific constraints on meeting times, we just need to ensure they are met
# If the solver finds a solution that meets all constraints, it means we've met all friends we can

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        print(f"Arrive at {loc} at {model[start_times[loc]] // 60}:{model[start_times[loc]] % 60:02}")
else:
    print("No solution found")