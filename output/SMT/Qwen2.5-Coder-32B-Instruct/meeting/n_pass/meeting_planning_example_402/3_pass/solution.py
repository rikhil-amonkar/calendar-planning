from z3 import *

# Define the locations and their travel times in minutes
locations = ["Golden Gate Park", "Haight-Ashbury", "Sunset District", "Marina District", "Financial District", "Union Square"]
travel_times = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
}

# Define the friends and their availability in minutes from 00:00
friends = {
    "Sarah": {"location": "Haight-Ashbury", "start": 17*60, "end": 21*60+30, "min_duration": 105},
    "Patricia": {"location": "Sunset District", "start": 17*60, "end": 19*60+45, "min_duration": 45},
    "Matthew": {"location": "Marina District", "start": 9*60+15, "end": 12*60, "min_duration": 15},
    "Joseph": {"location": "Financial District", "start": 14*60+15, "end": 18*60+45, "min_duration": 30},
    "Robert": {"location": "Union Square", "start": 10*60+15, "end": 21*60+45, "min_duration": 15},
}

# Create a solver instance
solver = Solver()

# Define the start time for the day in minutes from 00:00
start_time = 9*60  # 9:00 AM

# Define variables for the start and end times of each meeting
meeting_vars = {}
for friend, details in friends.items():
    meeting_vars[friend] = (Int(f"{friend}_start"), Int(f"{friend}_end"))

# Define the current location and time
current_location = "Golden Gate Park"
current_time = start_time

# Add constraints for each friend
for friend, (start, end) in meeting_vars.items():
    details = friends[friend]
    # Meeting must start after the current time and before the friend's availability ends
    solver.add(start >= current_time)
    solver.add(start + details["min_duration"] <= details["end"])
    # Meeting must end after the minimum duration and before the friend's availability ends
    solver.add(end >= start + details["min_duration"])
    solver.add(end <= details["end"])
    # Travel time to the friend's location
    travel_time = travel_times[(current_location, details["location"])]
    solver.add(start >= current_time + travel_time)
    # Update the current location and time
    current_location = details["location"]
    current_time = end

# Add constraints to ensure the order of meetings is feasible
# We need to ensure that the end time of one meeting plus travel time to the next location is less than or equal to the start time of the next meeting
friends_list = list(friends.keys())
for i in range(len(friends_list) - 1):
    current_friend = friends_list[i]
    next_friend = friends_list[i + 1]
    current_end = meeting_vars[current_friend][1]
    next_start = meeting_vars[next_friend][0]
    travel_time = travel_times[(friends[current_friend]["location"], friends[next_friend]["location"])]
    solver.add(next_start >= current_end + travel_time)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend, (start, end) in meeting_vars.items():
        start_time_minutes = model.evaluate(start).as_long()
        end_time_minutes = model.evaluate(end).as_long()
        start_time_str = f"{start_time_minutes // 60:02}:{start_time_minutes % 60:02}"
        end_time_str = f"{end_time_minutes // 60:02}:{end_time_minutes % 60:02}"
        itinerary.append({"action": "meet", "person": friend, "start_time": start_time_str, "end_time": end_time_str})
    print({"itinerary": itinerary})
else:
    print("No solution found")