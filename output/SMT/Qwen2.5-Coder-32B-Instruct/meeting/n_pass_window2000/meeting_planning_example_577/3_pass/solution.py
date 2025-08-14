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

# Define the location at each time step
location_at_time = {t: String(f"location_at_{t}") for t in range(9*60, 22*60)}

# Add constraints for each friend meeting
for name, details in friends.items():
    start = meeting_starts[name]
    solver.add(start >= details["start"])
    solver.add(start + details["min_meeting"] <= details["end"])
    # Round start time to the nearest minute in location_at_time
    rounded_start = Int(f"rounded_start_{name}")
    solver.add(rounded_start == start)
    solver.add(location_at_time[rounded_start] == details["location"])
    solver.add(location_at_time[rounded_start + details["min_meeting"] - 1] == details["location"])

# Add constraints for travel times
for t in range(9*60, 22*60 - 1):
    for loc1 in locations:
        for loc2 in locations:
            if loc1 != loc2:
                # Ensure that if you are at loc1 at time t, you can only be at loc2 at time t+1 if you have enough time to travel
                solver.add(Or(location_at_time[t] != loc1, location_at_time[t + 1] == loc1, 
                               location_at_time[t + 1] == loc2, t + travel_times[(loc1, loc2)] >= 22*60))

# Add initial location constraint
solver.add(location_at_time[9*60] == "Haight-Ashbury")

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in friends.items():
        start_time = model[meeting_starts[name]].as_long()
        end_time = start_time + details["min_meeting"]
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")