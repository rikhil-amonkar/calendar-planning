from z3 import *

# Define the locations and their travel times in minutes
locations = ["Sunset District", "North Beach", "Union Square", "Alamo Square"]
travel_times = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# Define the friends and their availability in minutes since 9:00 AM
friends = {
    "Sarah": {"location": "North Beach", "start": 420, "end": 555, "min_duration": 60},
    "Jeffrey": {"location": "Union Square", "start": 360, "end": 720, "min_duration": 75},
    "Brian": {"location": "Alamo Square", "start": 420, "end": 450, "min_duration": 75},
}

# Define the start time in minutes since 9:00 AM
start_time = 0  # 9:00 AM

# Define a function to convert minutes since start of the day to HH:MM format
def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{int(hours):02}:{int(minutes):02}"

# Define the sequence of meetings
sequence = ["Jeffrey", "Brian", "Sarah"]

# Create a solver
solver = Solver()

# Define the variables for the start and end times of each meeting in minutes
meeting_start = {name: Int(name + "_start") for name in sequence}
meeting_end = {name: Int(name + "_end") for name in sequence}

# Add constraints for each friend
for name in sequence:
    details = friends[name]
    # Meeting must start after the friend is available
    solver.add(meeting_start[name] >= details["start"])
    # Meeting must end before the friend is unavailable
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])

# Define the current location and time
current_location = "Sunset District"
current_time = start_time

# Add constraints for travel times
for name in sequence:
    details = friends[name]
    # Travel time from current location to friend's location
    travel_time = travel_times[(current_location, details["location"])]
    # Meeting must start after arriving at the friend's location
    solver.add(meeting_start[name] >= current_time + travel_time)
    # Update current location and time
    current_location = details["location"]
    current_time = meeting_start[name] + details["min_duration"]

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in sequence:
        start = model[meeting_start[name]].as_long()
        end = model[meeting_end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")