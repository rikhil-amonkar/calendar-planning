from z3 import *

# Define the locations
locations = ["Sunset District", "Alamo Square", "Russian Hill", "Golden Gate Park", "Mission District"]

# Define the travel times in minutes
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

# Define the friends and their availability
friends = {
    "Charles": {"location": "Alamo Square", "start": 1800, "end": 2025, "min_duration": 90},
    "Margaret": {"location": "Russian Hill", "start": 900, "end": 1600, "min_duration": 30},
    "Daniel": {"location": "Golden Gate Park", "start": 800, "end": 1330, "min_duration": 15},
    "Stephanie": {"location": "Mission District", "start": 2030, "end": 2200, "min_duration": 90},
}

# Convert times to minutes from 00:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Define the start time
start_time = time_to_minutes("09:00")

# Create a solver
solver = Solver()

# Define variables for meeting start and end times
meeting_start = {name: Int(f"{name}_start") for name in friends}
meeting_end = {name: Int(f"{name}_end") for name in friends}

# Define the order of meetings: Daniel -> Margaret -> Charles -> Stephanie
order = ["Daniel", "Margaret", "Charles", "Stephanie"]

# Constraints for each friend in the defined order
for i, name in enumerate(order):
    details = friends[name]
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Meeting must start and end within the friend's availability
    solver.add(meeting_start[name] >= start)
    solver.add(meeting_end[name] <= end)
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= min_duration)
    
    # Travel time constraints
    if i > 0:
        prev_name = order[i - 1]
        prev_loc = friends[prev_name]["location"]
        travel_time = travel_times[(prev_loc, loc)]
        solver.add(meeting_end[prev_name] + travel_time <= meeting_start[name])
    else:
        # Ensure we can reach the first friend by their start time
        travel_time = travel_times[("Sunset District", loc)]
        solver.add(start_time + travel_time <= meeting_start[name])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in order:
        start = model[meeting_start[name]].as_long()
        end = model[meeting_end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print({"itinerary": itinerary})
else:
    print("No solution found")