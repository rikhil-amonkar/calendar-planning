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

# Add travel times for traveling from a location to itself
for location in locations:
    travel_times[(location, location)] = 0

# Define the friends and their availability
friends = {
    "Mary": {"location": "Golden Gate Park", "start": 8.75, "end": 11.75, "min_duration": 0.75},
    "Kevin": {"location": "Haight-Ashbury", "start": 10.25, "end": 16.25, "min_duration": 1.5},
    "Deborah": {"location": "Bayview", "start": 15.0, "end": 19.25, "min_duration": 2.0},
    "Stephanie": {"location": "Presidio", "start": 10.0, "end": 17.25, "min_duration": 2.0},
    "Emily": {"location": "Financial District", "start": 11.5, "end": 21.75, "min_duration": 1.75},
}

# Create an optimizer instance
optimizer = Optimize()

# Define the start time for each friend meeting
start_times = {name: Real(name + "_start") for name in friends}

# Define the end time for each friend meeting
end_times = {name: Real(name + "_end") for name in friends}

# Define the location for each friend meeting
locations_vars = {name: Int(name + "_location") for name in friends}

# Define the constraints
for name, details in friends.items():
    # Meeting must start after the friend is available
    optimizer.add(start_times[name] >= details["start"])
    # Meeting must end before the friend is unavailable
    optimizer.add(end_times[name] <= details["end"])
    # Meeting must last at least the minimum duration
    optimizer.add(end_times[name] - start_times[name] >= details["min_duration"])
    # Meeting location must match the friend's location
    optimizer.add(locations_vars[name] == locations.index(details["location"]))

# Define the travel constraints
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            # If meeting with name1 ends before meeting with name2 starts, the travel time must be considered
            travel_time = travel_times[(locations[locations.index(friends[name1]["location"])], locations[locations.index(friends[name2]["location"])])]
            optimizer.add(Or(end_times[name1] + travel_time / 60.0 <= start_times[name2],
                              end_times[name2] + travel_time / 60.0 <= start_times[name1]))

# Define the initial location and time
initial_location = locations.index("Embarcadero")
initial_time = 9.0
optimizer.add(start_times[min(friends, key=lambda name: friends[name]["start"])] >= initial_time + travel_times[(locations[initial_location], locations[locations.index(friends[min(friends, key=lambda name: friends[name]["start"])]["location"])])] / 60.0)

# Solve the problem
if optimizer.check() == sat:
    model = optimizer.model()
    itinerary = []
    for name in friends:
        start = model[start_times[name]].as_fraction()
        end = model[end_times[name]].as_fraction()
        start_hour = int(start.numerator / start.denominator)
        start_minute = int(((start.numerator / start.denominator) % 1) * 60)
        end_hour = int(end.numerator / end.denominator)
        end_minute = int(((end.numerator / end.denominator) % 1) * 60)
        itinerary.append({"action": "meet", "person": name, "start_time": f"{start_hour:02}:{start_minute:02}", "end_time": f"{end_hour:02}:{end_minute:02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")