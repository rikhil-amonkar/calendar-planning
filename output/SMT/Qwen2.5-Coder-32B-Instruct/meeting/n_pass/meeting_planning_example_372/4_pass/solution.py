from z3 import *

# Define the locations
locations = ["Sunset District", "Alamo Square", "Russian Hill", "Golden Gate Park", "Mission District"]

# Define the travel times in minutes
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

# Define the friends and their availability
friends = {
    "Charles": {"location": "Alamo Square", "start": 1800, "end": 2025, "min_duration": 90},
    "Margaret": {"location": "Russian Hill", "start": 900, "end": 1600, "min_duration": 30},
    "Daniel": {"location": "Golden Gate Park", "start": 800, "end": 1330, "min_duration": 15},
    "Stephanie": {"location": "Mission District", "start": 2030, "end": 2200, "min_duration": 90},
}

# Convert times to minutes from 00:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Define the start time
start_time = time_to_minutes("09:00")

# Create a solver
solver = Solver()

# Define variables for meeting start and end times
meeting_start = {name: Int(f"start_{name}") for name in friends}
meeting_end = {name: Int(f"end_{name}") for name in friends}

# Define the initial location
initial_location = "Sunset District"

# Add constraints for each friend
for i, (name, details) in enumerate(friends.items()):
    # Meeting must start after the person is available and end before they leave
    solver.add(meeting_start[name] >= details["start"])
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])
    # Meeting must start after the previous meeting ends and after travel time
    if i > 0:
        prev_name = list(friends.keys())[i - 1]
        prev_location = friends[prev_name]["location"]
        current_location = friends[name]["location"]
        travel_time = travel_times[(prev_location, current_location)]
        solver.add(meeting_start[name] >= meeting_end[prev_name] + travel_time)
    else:
        # First meeting must start after the initial travel time from Sunset District
        current_location = friends[name]["location"]
        travel_time = travel_times[(initial_location, current_location)]
        solver.add(meeting_start[name] >= start_time + travel_time)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
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