from z3 import *

# Define the locations and their travel times
locations = ["Fisherman's Wharf", "Golden Gate Park", "Presidio", "Richmond District"]
travel_times = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
}

# Define the friends and their availability
friends = {
    "Melissa": {"location": "Golden Gate Park", "start": 8.5, "end": 20.0, "min_duration": 0.25},
    "Nancy": {"location": "Presidio", "start": 19.75, "end": 22.0, "min_duration": 1.75},
    "Emily": {"location": "Richmond District", "start": 16.75, "end": 22.0, "min_duration": 2.0},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    return int(time * 60)

# Create a solver instance
solver = Solver()

# Define the start time at Fisherman's Wharf
start_time = time_to_minutes(9.0)

# Define variables for meeting start and end times
meeting_start = {friend: Int(f"{friend}_start") for friend in friends}
meeting_end = {friend: Int(f"{friend}_end") for friend in friends}

# Define the location of each friend
location = {friend: friends[friend]["location"] for friend in friends}

# Add constraints for each friend
for friend in friends:
    # Meeting must start after the friend is available
    solver.add(meeting_start[friend] >= time_to_minutes(friends[friend]["start"]))
    # Meeting must end before the friend is unavailable
    solver.add(meeting_end[friend] <= time_to_minutes(friends[friend]["end"]))
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[friend] - meeting_start[friend] >= time_to_minutes(friends[friend]["min_duration"]))

# Add constraints for travel times between meetings
# We assume we can only meet one friend at a time and we start at Fisherman's Wharf
current_location = "Fisherman's Wharf"
current_time = start_time

# Sort friends by their start time to try to meet them in order
sorted_friends = sorted(friends.keys(), key=lambda x: friends[x]["start"])

for i, friend in enumerate(sorted_friends):
    # Travel time to the friend's location
    travel_time = travel_times[(current_location, location[friend])]
    # Meeting can only start after we arrive at the location
    solver.add(meeting_start[friend] >= current_time + travel_time)
    # Update current location and time
    current_location = location[friend]
    current_time = meeting_end[friend]

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend in sorted_friends:
        start = model[meeting_start[friend]].as_long() / 60
        end = model[meeting_end[friend]].as_long() / 60
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")