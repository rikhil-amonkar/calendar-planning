from z3 import *

# Define the locations
locations = ["Haight-Ashbury", "Russian Hill", "Fisherman's Wharf", "Nob Hill", "Golden Gate Park", "Alamo Square", "Pacific Heights"]

# Define the travel times in minutes
travel_times = {
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
}

# Define the friends and their availability
friends = {
    "Stephanie": {"location": "Russian Hill", "start": 20*60, "end": 20*60 + 45, "min_meeting": 15},
    "Kevin": {"location": "Fisherman's Wharf", "start": 19*60 + 15, "end": 21*60 + 45, "min_meeting": 75},
    "Robert": {"location": "Nob Hill", "start": 7*60 + 45, "end": 10*60 + 30, "min_meeting": 90},
    "Steven": {"location": "Golden Gate Park", "start": 8*60 + 30, "end": 17*60, "min_meeting": 75},
    "Anthony": {"location": "Alamo Square", "start": 7*60 + 45, "end": 19*60 + 45, "min_meeting": 15},
    "Sandra": {"location": "Pacific Heights", "start": 14*60 + 45, "end": 21*60 + 45, "min_meeting": 45},
}

# Create a solver
solver = Solver()

# Define the start time for each friend meeting
meeting_starts = {name: Int(f"start_{name}") for name in friends}

# Define the location at each meeting start time
location_at_meeting_start = {name: String(f"location_at_start_{name}") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    start, end, min_meeting = details["start"], details["end"], details["min_meeting"]
    solver.add(meeting_starts[name] >= start)
    solver.add(meeting_starts[name] + min_meeting <= end)
    solver.add(location_at_meeting_start[name] == details["location"])

# Add constraints for travel times
for i, name1 in enumerate(friends):
    for name2 in list(friends)[i+1:]:
        start1, end1 = meeting_starts[name1], meeting_starts[name1] + friends[name1]["min_meeting"]
        start2, end2 = meeting_starts[name2], meeting_starts[name2] + friends[name2]["min_meeting"]
        loc1, loc2 = friends[name1]["location"], friends[name2]["location"]
        travel_time = travel_times[(loc1, loc2)]
        solver.add(Or(start1 + end1 + travel_time <= start2, start2 + end2 + travel_time <= start1))

# Add initial location constraint
solver.add(location_at_meeting_start["Robert"] == "Nob Hill")

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in friends.items():
        start_time = model[meeting_starts[name]].as_long()
        end_time = start_time + details["min_meeting"]
        itinerary.append({"action": "meet", "person": name, "start_time": f"{start_time//60:02}:{start_time%60:02}", "end_time": f"{end_time//60:02}:{end_time%60:02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")