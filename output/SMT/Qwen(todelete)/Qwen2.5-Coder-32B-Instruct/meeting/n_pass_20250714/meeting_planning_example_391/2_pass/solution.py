from z3 import *

# Define the locations
locations = ["Sunset District", "Alamo Square", "Russian Hill", "Presidio", "Financial District"]

# Define the travel times in minutes
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

# Define the friends' availability and meeting requirements
friends = {
    "Kevin": {"location": "Alamo Square", "start": 8*60 + 15, "end": 21*60 + 30, "min_meeting": 75},
    "Kimberly": {"location": "Russian Hill", "start": 8*60 + 45, "end": 12*60 + 30, "min_meeting": 30},
    "Joseph": {"location": "Presidio", "start": 18*60 + 30, "end": 19*60 + 15, "min_meeting": 45},
    "Thomas": {"location": "Financial District", "start": 19*60, "end": 21*60 + 45, "min_meeting": 45},
}

# Create a solver instance
solver = Solver()

# Define variables for the start time at each location
start_times = {loc: Int(f"start_{loc}") for loc in locations}

# Define binary variables for meeting each friend
meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends}

# Add constraints for the start times
for loc in locations:
    solver.add(start_times[loc] >= 0)

# Start at Sunset District at 9:00 AM (540 minutes)
solver.add(start_times["Sunset District"] == 540)

# Add constraints for meeting each friend
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_meeting = details["min_meeting"]
    
    # Define the end time at the friend's location
    end_time_at_loc = start_times[loc] + min_meeting
    
    # Ensure we arrive at the friend's location before they leave
    solver.add(Implies(meet_friends[friend], end_time_at_loc <= end))
    
    # Ensure we leave the friend's location after they arrive
    solver.add(Implies(meet_friends[friend], start_times[loc] + min_meeting >= start))
    
    # Ensure we have enough time to travel to the next location
    for next_loc in locations:
        if next_loc != loc:
            travel_time = travel_times[(loc, next_loc)]
            solver.add(Implies(meet_friends[friend], start_times[next_loc] >= start_times[loc] + min_meeting + travel_time))

# Ensure we meet exactly 4 friends
solver.add(Sum([If(meet_friends[friend], 1, 0) for friend in friends]) == 4)

# Add constraints to ensure we can visit all required locations within the day
max_time = 24 * 60  # 24 hours in minutes
for loc in locations:
    solver.add(start_times[loc] <= max_time)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        print(f"Start time at {loc}: {model[start_times[loc]]} minutes (or {model[start_times[loc]] // 60}:{model[start_times[loc]] % 60:02d})")
    for friend in friends:
        if model.evaluate(meet_friends[friend]):
            print(f"Meet {friend} at {friends[friend]['location']} from {model[start_times[friends[friend]['location']]]} to {model[start_times[friends[friend]['location']]] + friends[friend]['min_meeting']}")
else:
    print("No solution found.")