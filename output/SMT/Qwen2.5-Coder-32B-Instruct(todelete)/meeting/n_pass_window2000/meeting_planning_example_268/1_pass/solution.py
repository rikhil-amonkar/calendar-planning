from z3 import *

# Define the locations
locations = ["Golden Gate Park", "Alamo Square", "Presidio", "Russian Hill"]

# Define the travel times in minutes
travel_times = {
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Russian Hill"): 13,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
}

# Define the friends and their availability
friends = {
    "Timothy": {"location": "Alamo Square", "start": 12*60, "end": 16*60 + 15, "min_duration": 105},
    "Mark": {"location": "Presidio", "start": 18*60 + 45, "end": 21*60, "min_duration": 60},
    "Joseph": {"location": "Russian Hill", "start": 16*60 + 45, "end": 21*60 + 30, "min_duration": 60},
}

# Create a solver
solver = Solver()

# Define the start time of the day in minutes (9:00 AM)
start_time = 9 * 60

# Define the variables for the start and end times of each meeting
meeting_start = {name: Int(f"start_{name}") for name in friends}
meeting_end = {name: Int(f"end_{name}") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the person is available
    solver.add(meeting_start[name] >= details["start"])
    # Meeting must end before the person is unavailable
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])

# Define the current location and time
current_location = "Golden Gate Park"
current_time = start_time

# Add constraints for travel times
for name, details in friends.items():
    # Travel time from current location to friend's location
    travel_time = travel_times[(current_location, details["location"])]
    # Meeting must start after arriving at the location
    solver.add(meeting_start[name] >= current_time + travel_time)
    # Update current location and time after meeting
    current_location = details["location"]
    current_time = meeting_end[name]

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in friends.items():
        start = model[meeting_start[name]].as_long()
        end = model[meeting_end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")