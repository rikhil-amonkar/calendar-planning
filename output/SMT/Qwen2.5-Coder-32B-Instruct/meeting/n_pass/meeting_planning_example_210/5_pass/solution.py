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
for i, (name1, details1) in enumerate(friends.items()):
    for name2, details2 in list(friends.items())[i+1:]:
        # Travel time from details1's location to details2's location
        travel_time_1_to_2 = travel_times[(locations[details1["location"]], locations[details2["location"]])]
        travel_time_2_to_1 = travel_times[(locations[details2["location"]], locations[details1["location"]])]
        
        # Ensure that if meeting with name1 ends before meeting with name2 starts, travel time is respected
        optimizer.add(Or(end_times[name1] + travel_time_1_to_2 / 60 <= start_times[name2],
                         end_times[name2] + travel_time_2_to_1 / 60 <= start_times[name1]))

# Define the objective: maximize the number of meetings
objective = Sum([If(start_times[name] < end_times[name], 1, 0) for name in friends])

# Optimize the solver
optimizer.maximize(objective)

# Check if the problem is solvable
if optimizer.check() == sat:
    model = optimizer.model()
    itinerary = []
    for name, details in friends.items():
        start = model.evaluate(start_times[name]).as_decimal(2)
        end = model.evaluate(end_times[name]).as_decimal(2)
        if start < end:
            start_hour = int(float(str(start)))
            start_minute = int((float(str(start)) % 1) * 60)
            end_hour = int(float(str(end)))
            end_minute = int((float(str(end)) % 1) * 60)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02}:{start_minute:02}",
                "end_time": f"{end_hour:02}:{end_minute:02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")