from z3 import *

# Define the locations and their travel times
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

# Define the friends and their availability
friends = {
    "Sarah": {"location": "North Beach", "start": 16, "end": 18.25, "min_duration": 1},
    "Jeffrey": {"location": "Union Square", "start": 15, "end": 22, "min_duration": 1.25},
    "Brian": {"location": "Alamo Square", "start": 16, "end": 17.5, "min_duration": 1.25},
}

# Define the start time
start_time = 9  # 9:00 AM

# Create a solver
solver = Solver()

# Define the variables for the start and end times of each meeting
meeting_start = {name: Real(name + "_start") for name in friends}
meeting_end = {name: Real(name + "_end") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the friend is available
    solver.add(meeting_start[name] >= details["start"])
    # Meeting must end before the friend is unavailable
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])

# Define the current location and time
current_location = "Sunset District"
current_time = start_time

# Define a function to convert time to minutes since start of the day
def time_to_minutes(time):
    return int(time * 60)

# Define a function to convert minutes since start of the day to HH:MM format
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{int(hours):02}:{int(minutes):02}"

# Add constraints for travel times
for name, details in friends.items():
    # Travel time from current location to friend's location
    travel_time = travel_times[(current_location, details["location"])]
    # Meeting must start after arriving at the friend's location
    solver.add(meeting_start[name] >= current_time + travel_time / 60)
    # Update current location and time
    current_location = details["location"]
    current_time = meeting_start[name] + details["min_duration"]

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_start[name]].as_decimal(2)
        end = model[meeting_end[name]].as_decimal(2)
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(time_to_minutes(float(start))),
            "end_time": minutes_to_time(time_to_minutes(float(end)))
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")