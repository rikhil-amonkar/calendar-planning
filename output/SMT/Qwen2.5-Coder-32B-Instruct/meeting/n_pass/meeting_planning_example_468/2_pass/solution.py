from z3 import *

# Define the locations
locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", "Fisherman's Wharf", "Golden Gate Park"]

# Define the travel times in minutes
travel_times = {
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,
    ("Bayview", "The Castro"): 20,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
}

# Define the friends and their availability
friends = {
    "Rebecca": {"location": "Bayview", "start": 9*60, "end": 12*60 + 45, "min_duration": 90},
    "Amanda": {"location": "Pacific Heights", "start": 18*60 + 30, "end": 21*60 + 45, "min_duration": 90},
    "James": {"location": "Alamo Square", "start": 9*60 + 45, "end": 21*60 + 15, "min_duration": 90},
    "Sarah": {"location": "Fisherman's Wharf", "start": 8*60, "end": 21*30, "min_duration": 90},
    "Melissa": {"location": "Golden Gate Park", "start": 9*60, "end": 18*45, "min_duration": 90},
}

# Create a solver
solver = Solver()

# Define the start time for each friend meeting
meeting_starts = {name: Int(f"start_{name}") for name in friends}

# Define the location at each time step
current_location = Int("current_location")

# Initial location is The Castro at 9:00 AM
solver.add(current_location == locations.index("The Castro"))
solver.add(meeting_starts["Rebecca"] >= 9*60)

# Add constraints for each friend
for name, details in friends.items():
    start = meeting_starts[name]
    end = start + details["min_duration"]
    solver.add(start >= details["start"])
    solver.add(end <= details["end"])
    solver.add(current_location == locations.index(details["location"]))

# Add travel time constraints
for i in range(len(friends) - 1):
    name1, name2 = list(friends.keys())[i], list(friends.keys())[i + 1]
    start1, end1 = meeting_starts[name1], meeting_starts[name1] + friends[name1]["min_duration"]
    start2, end2 = meeting_starts[name2], meeting_starts[name2] + friends[name2]["min_duration"]
    travel_time = travel_times[(friends[name1]["location"], friends[name2]["location"])]
    solver.add(end1 + travel_time <= start2)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends.keys():
        start_time = model[meeting_starts[name]].as_long()
        end_time = start_time + friends[name]["min_duration"]
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