from z3 import *

# Define the locations and their travel times in minutes
locations = ["Sunset District", "Chinatown", "Russian Hill", "North Beach"]
travel_times = {
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
}

# Define the friends and their availability in 24-hour format (as hours)
friends = {
    "Anthony": {"location": "Chinatown", "start": 13.25, "end": 14.5},
    "Rebecca": {"location": "Russian Hill", "start": 19.5, "end": 21.25},
    "Melissa": {"location": "North Beach", "start": 8.25, "end": 13.5},
}

# Define the minimum meeting times in hours
min_meeting_times = {
    "Anthony": 1.0,
    "Rebecca": 1.75,
    "Melissa": 1.75,
}

# Define the start time in hours
start_time = 9.0

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start_times = {friend: Real(f"start_{friend}") for friend in friends}
meeting_end_times = {friend: Real(f"end_{friend}") for friend in friends}

# Define the order of meetings
order = ["Melissa", "Anthony", "Rebecca"]

# Define the current location and time
current_location = "Sunset District"
current_time = start_time

# Add constraints for each friend in the specified order
for friend in order:
    details = friends[friend]
    # Meeting must start after the friend is available
    solver.add(meeting_start_times[friend] >= details["start"])
    # Meeting must end before the friend is unavailable
    solver.add(meeting_end_times[friend] <= details["end"])
    # Meeting must last at least the minimum required time
    solver.add(meeting_end_times[friend] - meeting_start_times[friend] >= min_meeting_times[friend])

    # Travel time from current location to friend's location
    travel_time = travel_times[(current_location, details["location"])] / 60.0
    # Meeting must start after arriving at the friend's location
    solver.add(meeting_start_times[friend] >= current_time + travel_time)
    # Update current location and time
    current_location = details["location"]
    current_time = meeting_end_times[friend]

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend in order:
        start_time = model[meeting_start_times[friend]].as_decimal(2)
        end_time = model[meeting_end_times[friend]].as_decimal(2)
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{int(start_time):02}:{int((start_time % 1) * 60):02}",
            "end_time": f"{int(end_time):02}:{int((end_time % 1) * 60):02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")