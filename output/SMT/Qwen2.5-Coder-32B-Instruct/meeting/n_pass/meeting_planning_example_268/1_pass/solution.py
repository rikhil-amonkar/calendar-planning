from z3 import *

# Define the locations
locations = ["Golden Gate Park", "Alamo Square", "Presidio", "Russian Hill"]

# Define the travel times in minutes
travel_times = {
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Russian Hill"): 13,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
}

# Define the friends and their availability
friends = {
    "Timothy": {"location": "Alamo Square", "start": 12*60, "end": 16*60 + 15, "min_duration": 105},
    "Mark": {"location": "Presidio", "start": 18*60 + 45, "end": 21*60, "min_duration": 60},
    "Joseph": {"location": "Russian Hill", "start": 16*60 + 45, "end": 21*60 + 30, "min_duration": 60},
}

# Create a solver
solver = Solver()

# Define the start time for each friend meeting
start_times = {name: Int(f"start_{name}") for name in friends}

# Define the end time for each friend meeting
end_times = {name: Int(f"end_{name}") for name in friends}

# Define the current location
current_location = "Golden Gate Park"
current_time = 9*60  # 9:00 AM in minutes

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the current time and before the friend's availability ends
    solver.add(start_times[name] >= current_time)
    solver.add(start_times[name] >= details["start"])
    solver.add(end_times[name] <= details["end"])
    
    # Meeting must last at least the minimum duration
    solver.add(end_times[name] - start_times[name] >= details["min_duration"])
    
    # Travel time to the friend's location
    travel_time = travel_times[(current_location, details["location"])]
    solver.add(start_times[name] >= current_time + travel_time)
    
    # Update current time and location
    current_time = end_times[name]
    current_location = details["location"]

# Define the objective: maximize the number of meetings
# Since we have constraints on meeting durations, we just need to find a feasible schedule
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[start_times[name]].as_long()
        end = model[end_times[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start//60:02}:{start%60:02}",
            "end_time": f"{end//60:02}:{end%60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")