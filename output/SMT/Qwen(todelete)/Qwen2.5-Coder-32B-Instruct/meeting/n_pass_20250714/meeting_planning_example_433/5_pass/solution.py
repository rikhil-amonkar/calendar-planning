from z3 import *

# Define the locations
locations = ["Nob Hill", "Richmond District", "Financial District", "North Beach", "The Castro", "Golden Gate Park"]

# Define the travel times in minutes
travel_times = {
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# Define the friends' availability and meeting requirements
friends = {
    "Emily": {"location": "Richmond District", "start": 7*60 + 0, "end": 9*60 + 0, "min_meeting_time": 15},
    "Margaret": {"location": "Financial District", "start": 4*60 + 30, "end": 8*60 + 15, "min_meeting_time": 75},
    "Ronald": {"location": "North Beach", "start": 6*60 + 30, "end": 7*60 + 30, "min_meeting_time": 45},
    "Deborah": {"location": "The Castro", "start": 1*60 + 45, "end": 9*60 + 15, "min_meeting_time": 90},
    "Jeffrey": {"location": "Golden Gate Park", "start": 11*60 + 15, "end": 2*60 + 30, "min_meeting_time": 120},
}

# Create a solver instance
solver = Solver()

# Define variables for each friend's meeting time
meeting_start_times = {name: Int(f"{name}_start") for name in friends}
meeting_end_times = {name: Int(f"{name}_end") for name in friends}

# Define a sequence of visits
visit_order = [String(f"visit_{i}") for i in range(len(friends))]
visit_times = [Int(f"time_{i}") for i in range(len(friends))]

# Add constraints for each friend
for i, (name, details) in enumerate(friends.items()):
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_meeting_time = details["min_meeting_time"]
    
    # Meeting must start after or when the friend is available
    solver.add(meeting_start_times[name] >= start)
    # Meeting must end before or when the friend is available
    solver.add(meeting_end_times[name] <= end)
    # Meeting duration must be at least the minimum required
    solver.add(meeting_end_times[name] - meeting_start_times[name] >= min_meeting_time)
    
    # Visit order constraints
    solver.add(visit_order[i] == location)
    solver.add(visit_times[i] == meeting_end_times[name])

# Initial conditions
solver.add(visit_order[0] == "Nob Hill")
solver.add(visit_times[0] == 9*60)  # Start at 9:00 AM

# Add constraints for traveling between locations
for i in range(len(friends) - 1):
    current_location = visit_order[i]
    next_location = visit_order[i + 1]
    current_time = visit_times[i]
    next_time = visit_times[i + 1]
    
    # Travel time constraint
    solver.add(next_time == current_time + If(current_location == next_location, 0, 
                                              travel_times[(current_location, next_location)]))

# Ensure each location is visited exactly once
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        solver.add(visit_order[i] != visit_order[j])

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for i in range(len(friends)):
        location = model[visit_order[i]].as_string().strip('"')
        end_time = model[visit_times[i]].as_long()
        start_time = end_time - friends[list(friends.keys())[i]]["min_meeting_time"]
        print(f"Visit {location} from {start_time // 60}:{start_time % 60:02d} to {end_time // 60}:{end_time % 60:02d}")
else:
    print("No solution found.")