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

# Create an optimizer instance
optimizer = Optimize()

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
    optimizer.add(start_times[name] >= details["start"])
    optimizer.add(start_times[name] <= details["end"] - details["min_duration"])
    
    # End time must be within the friend's availability
    optimizer.add(end_times[name] >= start_times[name] + details["min_duration"])
    optimizer.add(end_times[name] <= details["end"])
    
    # Location constraint
    optimizer.add(locations_vars[name] == location_map[details["location"]])

# Define the current location and time
current_location = location_map["Fisherman's Wharf"]
current_time = 9.0

# Add constraints for travel times
for name, details in friends.items():
    # Travel time from current location to friend's location
    travel_time = travel_times[(locations[current_location], details["location"])]
    optimizer.add(start_times[name] >= current_time + travel_time / 60)

# Define the objective: maximize the number of meetings
objective = Sum([If(start_times[name] < end_times[name], 1, 0) for name in friends])

# Optimize the solver
optimizer.maximize(objective)

# Check if the problem is solvable
if optimizer.check() == sat:
    model = optimizer.model()
    itinerary = []
    for name, details in friends.items():
        start = model[start_times[name]].as_decimal(2)
        end = model[end_times[name]].as_decimal(2)
        if start < end:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
                "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")