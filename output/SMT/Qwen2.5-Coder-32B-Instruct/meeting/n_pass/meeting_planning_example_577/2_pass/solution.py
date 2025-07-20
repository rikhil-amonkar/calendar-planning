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
start_times = {name: Int(f"start_{name}") for name in friends}

# Define the end time for each friend meeting
end_times = {name: Int(f"end_{name}") for name in friends}

# Define the location for each friend meeting
locations_vars = {name: Int(f"loc_{name}") for name in friends}

# Define the location mapping
location_map = {loc: i for i, loc in enumerate(locations)}

# Add constraints for each friend
for name, details in friends.items():
    loc = location_map[details["location"]]
    solver.add(locations_vars[name] == loc)
    solver.add(start_times[name] >= details["start"])
    solver.add(end_times[name] <= details["end"])
    solver.add(end_times[name] - start_times[name] >= details["min_meeting"])

# Add constraints for travel times
for i in range(len(friends) - 1):
    name1, name2 = list(friends.keys())[i], list(friends.keys())[i + 1]
    loc1, loc2 = locations_vars[name1], locations_vars[name2]
    start2 = start_times[name2]
    end1 = end_times[name1]
    travel_time = If(loc1 == loc2, 0, travel_times[(locations[loc1.as_long()], locations[loc2.as_long()])])
    solver.add(start2 >= end1 + travel_time)

# Add constraint for starting at Haight-Ashbury at 9:00AM
solver.add(start_times[list(friends.keys())[0]] >= 9*60)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[start_times[name]].as_long()
        end = model[end_times[name]].as_long()
        itinerary.append({"action": "meet", "person": name, "start_time": f"{start//60:02}:{start%60:02}", "end_time": f"{end//60:02}:{end%60:02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")