from z3 import *

# Define the locations and their travel times
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

# Define the friends and their availability
friends = {
    "Anthony": {"location": "Chinatown", "start": 13.25, "end": 14.50, "min_duration": 1.00},
    "Rebecca": {"location": "Russian Hill", "start": 19.50, "end": 21.25, "min_duration": 1.75},
    "Melissa": {"location": "North Beach", "start": 8.25, "end": 13.50, "min_duration": 1.75},
}

# Define the start time
start_time = 9.00

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {name: Real(name + "_start") for name in friends}
meeting_end = {name: Real(name + "_end") for name in friends}

# Define variables for the location changes
location_change = {i: Int(f"location_change_{i}") for i in range(len(friends) + 1)}

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the person is available and end before they are not available
    solver.add(meeting_start[name] >= details["start"])
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])

# Add constraints for travel times
for i in range(len(friends)):
    current_location = location_change[i]
    next_location = location_change[i + 1]
    current_friend = list(friends.keys())[i]
    next_friend = list(friends.keys())[i + 1] if i + 1 < len(friends) else None
    
    # Ensure the location change is valid
    solver.add(Or([current_location == locations.index(loc) for loc in locations]))
    if next_friend:
        solver.add(Or([next_location == locations.index(loc) for loc in locations]))
        # Ensure the travel time is respected
        solver.add(meeting_start[next_friend] - meeting_end[current_friend] >= 
                   travel_times[(locations[current_location.as_long()], locations[next_location.as_long()])])

# Add constraints for the initial location and start time
solver.add(location_change[0] == locations.index("Sunset District"))
solver.add(meeting_start[list(friends.keys())[0]] >= start_time)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_start[name]].as_decimal(2)
        end = model[meeting_end[name]].as_decimal(2)
        itinerary.append({"action": "meet", "person": name, "start_time": f"{int(start):02}:{int((start % 1) * 60):02}", "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"})
    itinerary = sorted(itinerary, key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")