from z3 import *

# Define the locations
locations = ["Mission District", "The Castro", "Nob Hill", "Presidio", "Marina District", 
             "Pacific Heights", "Golden Gate Park", "Chinatown", "Richmond District"]

# Define the travel times as a dictionary
travel_times = {
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# Define the friends and their availability
friends = {
    "Lisa": {"location": "The Castro", "start": 19.25, "end": 21.25, "min_duration": 2},
    "Daniel": {"location": "Nob Hill", "start": 8.25, "end": 11.00, "min_duration": 0.25},
    "Elizabeth": {"location": "Presidio", "start": 21.25, "end": 22.25, "min_duration": 0.75},
    "Steven": {"location": "Marina District", "start": 16.50, "end": 20.75, "min_duration": 1.5},
    "Timothy": {"location": "Pacific Heights", "start": 12.00, "end": 18.00, "min_duration": 1.5},
    "Ashley": {"location": "Golden Gate Park", "start": 20.75, "end": 21.75, "min_duration": 1},
    "Kevin": {"location": "Chinatown", "start": 12.00, "end": 19.00, "min_duration": 0.5},
    "Betty": {"location": "Richmond District", "start": 13.25, "end": 15.75, "min_duration": 0.5},
}

# Create a solver
solver = Solver()

# Define the start time for each friend meeting
start_times = {name: Real(name + "_start") for name in friends}

# Define the end time for each friend meeting
end_times = {name: Real(name + "_end") for name in friends}

# Define the location for each friend meeting
locations_vars = {name: Int(name + "_location") for name in friends}

# Define the location mapping
location_map = {loc: i for i, loc in enumerate(locations)}

# Add constraints for each friend
for name, details in friends.items():
    # Start time must be within the friend's availability
    solver.add(start_times[name] >= details["start"])
    solver.add(start_times[name] <= details["end"] - details["min_duration"])
    
    # End time must be within the friend's availability
    solver.add(end_times[name] >= start_times[name] + details["min_duration"])
    solver.add(end_times[name] <= details["end"])
    
    # Location must match the friend's location
    solver.add(locations_vars[name] == location_map[details["location"]])

# Add constraints for travel times
for i in range(len(friends) - 1):
    name1, name2 = list(friends.keys())[i], list(friends.keys())[i + 1]
    loc1, loc2 = friends[name1]["location"], friends[name2]["location"]
    travel_time = travel_times[(loc1, loc2)]
    solver.add(start_times[name2] >= end_times[name1] + travel_time / 60.0)

# Add constraint for starting at Mission District at 9:00AM
solver.add(start_times[list(friends.keys())[0]] >= 9.0)

# Add constraint to ensure the meetings are in chronological order
for i in range(len(friends) - 1):
    name1, name2 = list(friends.keys())[i], list(friends.keys())[i + 1]
    solver.add(start_times[name2] >= end_times[name1])

# Optimize the schedule to meet as many friends as possible
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends.keys():
        start = model[start_times[name]].as_decimal(2)
        end = model[end_times[name]].as_decimal(2)
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")