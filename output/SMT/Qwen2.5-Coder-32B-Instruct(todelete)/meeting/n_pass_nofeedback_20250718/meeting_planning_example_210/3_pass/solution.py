from z3 import *

# Define the locations and their travel times
locations = ["Fisherman's Wharf", "Presidio", "Richmond District", "Financial District"]
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21
}

# Define the friends and their availability
friends = {
    "Emily": {"location": "Presidio", "start": 16.25, "end": 21.00, "min_duration": 105/60},
    "Joseph": {"location": "Richmond District", "start": 17.25, "end": 22.00, "min_duration": 120/60},
    "Melissa": {"location": "Financial District", "start": 15.75, "end": 19.75, "min_duration": 75/60}
}

# Create a solver instance
solver = Solver()

# Define the start time variable for each friend
start_times = {name: Real(name + "_start") for name in friends}

# Define the end time variable for each friend
end_times = {name: Real(name + "_end") for name in friends}

# Define the location variable for each friend
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
    
    # Location constraint
    solver.add(locations_vars[name] == location_map[details["location"]])

# Define the current location and time
current_location = location_map["Fisherman's Wharf"]
current_time = 9.0

# Define the travel time constraints
for name, details in friends.items():
    # Travel time from current location to friend's location
    travel_time = travel_times[(locations[current_location], details["location"])]
    solver.add(start_times[name] >= current_time + travel_time / 60)

# Ensure that meetings do not overlap and respect travel times
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            # Ensure that meetings do not overlap
            solver.add(Or(end_times[name1] <= start_times[name2], end_times[name2] <= start_times[name1]))
            # Ensure that travel time is respected between meetings
            travel_time_1_to_2 = travel_times[(friends[name1]["location"], friends[name2]["location"])]
            travel_time_2_to_1 = travel_times[(friends[name2]["location"], friends[name1]["location"])]
            solver.add(Or(end_times[name1] + travel_time_1_to_60 / 60 <= start_times[name2],
                          end_times[name2] + travel_time_2_to_1 / 60 <= start_times[name1]))

# Define the objective: maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(start_times[name] < end_times[name], 1, 0) for name in friends]))

# Solve the problem
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for name, details in friends.items():
        start = model[start_times[name]].as_decimal(2)
        end = model[end_times[name]].as_decimal(2)
        if start < end:
            start_hour = int(float(start))
            start_minute = int((float(start) % 1) * 60)
            end_hour = int(float(end))
            end_minute = int((float(end) % 1) * 60)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02}:{start_minute:02}",
                "end_time": f"{end_hour:02}:{end_minute:02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")