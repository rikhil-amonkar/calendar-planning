from z3 import *

# Define the locations and their travel times
locations = ["Embarcadero", "Golden Gate Park", "Haight-Ashbury", "Bayview", "Presidio", "Financial District"]
travel_times = {
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Financial District"): 19,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Presidio"): 22,
}

# Define the friends and their availability
friends = {
    "Mary": {"location": "Golden Gate Park", "start": 8.75, "end": 11.75, "min_duration": 0.75},
    "Kevin": {"location": "Haight-Ashbury", "start": 10.25, "end": 16.25, "min_duration": 1.5},
    "Deborah": {"location": "Bayview", "start": 15.0, "end": 19.25, "min_duration": 2.0},
    "Stephanie": {"location": "Presidio", "start": 10.0, "end": 17.25, "min_duration": 2.0},
    "Emily": {"location": "Financial District", "start": 11.5, "end": 21.75, "min_duration": 1.75},
}

# Create a solver instance
solver = Solver()

# Define the start time for each friend meeting
start_times = {name: Real(name + "_start") for name in friends}

# Define the end time for each friend meeting
end_times = {name: Real(name + "_end") for name in friends}

# Define the location for each friend meeting
locations_vars = {name: Int(name + "_location") for name in friends}

# Define the constraints
for name, details in friends.items():
    # Meeting must start after the friend is available
    solver.add(start_times[name] >= details["start"])
    # Meeting must end before the friend is unavailable
    solver.add(end_times[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(end_times[name] - start_times[name] >= details["min_duration"])
    # Meeting location must match the friend's location
    solver.add(locations_vars[name] == locations.index(details["location"]))

# Define the travel constraints
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            # If meeting with name1 ends before meeting with name2 starts, the travel time must be considered
            solver.add(Or(end_times[name1] + travel_times[(locations[locations_vars[name1].as_long()], locations[locations_vars[name2].as_long()])] <= start_times[name2],
                          end_times[name2] + travel_times[(locations[locations_vars[name2].as_long()], locations[locations_vars[name1].as_long()])] <= start_times[name1]))

# Define the initial location and time
initial_location = locations.index("Embarcadero")
initial_time = 9.0
solver.add(start_times[min(friends, key=start_times.get)] >= initial_time + travel_times[(locations[initial_location], locations[locations_vars[min(friends, key=start_times.get)].as_long()])])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[start_times[name]].as_decimal(2)
        end = model[end_times[name]].as_decimal(2)
        itinerary.append({"action": "meet", "person": name, "start_time": f"{int(start):02}:{int((start % 1) * 60):02}", "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")