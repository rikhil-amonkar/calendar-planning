from z3 import *

# Define the locations
locations = ["Russian Hill", "Marina District", "Financial District", "Alamo Square",
             "Golden Gate Park", "The Castro", "Bayview", "Sunset District",
             "Haight-Ashbury", "Nob Hill"]

# Define the travel times in minutes
travel_times = {
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Nob Hill"): 16,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Nob Hill"): 27,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Haight-Ashbury"): 13,
}

# Define the friends' availability and meeting duration requirements
friends_availability = {
    "Karen": {"location": "Financial District", "start": 9*60 + 30, "end": 12*60 + 45, "duration": 90},
    "Barbara": {"location": "Alamo Square", "start": 10*60, "end": 19*60 + 30, "duration": 90},
    "David": {"location": "The Castro", "start": 9*60, "end": 18*60, "duration": 120},
    "Kevin": {"location": "Sunset District", "start": 10*60, "end": 17*60 + 45, "duration": 120},
    "Matthew": {"location": "Haight-Ashbury", "start": 10*60 + 15, "end": 15*60 + 30, "duration": 45},
    "Andrew": {"location": "Nob Hill", "start": 11*60 + 45, "end": 16*60 + 45, "duration": 105},
    "Linda": {"location": "Bayview", "start": 18*60 + 15, "end": 19*60 + 45, "duration": 45},
    "Nancy": {"location": "Golden Gate Park", "start": 16*60 + 45, "end": 20*60, "duration": 105},
}

# Sort friends by their start time and availability
sorted_friends = sorted(friends_availability.items(), key=lambda x: (x[1]["start"], x[1]["end"] - x[1]["start"]))

# Create the solver
solver = Solver()

# Define variables for each friend's meeting start time
meeting_start_times = {name: Int(name) for name, _ in sorted_friends}

# Add constraints for each friend's meeting
for name, info in sorted_friends:
    # Meeting must start after the person is available
    solver.add(meeting_start_times[name] >= info["start"])
    # Meeting must end before the person leaves
    solver.add(meeting_start_times[name] + info["duration"] <= info["end"])

# Define variables for location changes
location_change_times = []
current_location = "Russian Hill"
current_time = 9 * 60  # Start time at Russian Hill

# Function to add constraints for moving between locations
def move_to_location(from_loc, to_loc, start_time):
    travel_time = travel_times[(from_loc, to_loc)]
    arrival_time = start_time + travel_time
    location_change_times.append((from_loc, to_loc, arrival_time))
    return arrival_time

# Add constraints for moving between locations and meeting friends
selected_friends = []
for name, info in sorted_friends:
    # Move to the friend's location
    current_time = move_to_location(current_location, info["location"], current_time)
    # Ensure we have enough time to meet the friend
    if current_time <= info["start"]:
        # Add the friend to the selected list
        selected_friends.append(name)
        # Meet the friend
        current_time = meeting_start_times[name] + info["duration"]
        # Update current location
        current_location = info["location"]
    else:
        # Skip the friend if we can't reach them on time
        continue

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for name in selected_friends:
        meeting_start = model[meeting_start_times[name]].as_long()
        meeting_end = meeting_start + friends_availability[name]["duration"]
        print(f"Meet {name} at {friends_availability[name]['location']} from {meeting_start//60}:{meeting_start%60:02d} to {meeting_end//60}:{meeting_end%60:02d}")
else:
    print("No feasible solution found")