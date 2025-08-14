from z3 import *

# Define the locations and their travel times
locations = ["North Beach", "Pacific Heights", "Chinatown", "Union Square", "Mission District", "Golden Gate Park", "Nob Hill"]
travel_times = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

# Define the friends and their availability
friends = {
    "James": {"location": "Pacific Heights", "start": 2000, "end": 2200, "min_duration": 120},
    "Robert": {"location": "Chinatown", "start": 1215, "end": 1645, "min_duration": 90},
    "Jeffrey": {"location": "Union Square", "start": 930, "end": 1530, "min_duration": 120},
    "Carol": {"location": "Mission District", "start": 1815, "end": 2115, "min_duration": 15},
    "Mark": {"location": "Golden Gate Park", "start": 1130, "end": 1745, "min_duration": 15},
    "Sandra": {"location": "Nob Hill", "start": 800, "end": 1530, "min_duration": 15},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    return time // 100 * 60 + time % 100

# Create a Z3 solver
solver = Solver()

# Define variables for meeting start and end times
meet_start = {name: Int(f"start_{name}") for name in friends}
meet_end = {name: Int(f"end_{name}") for name in friends}

# Define variables for location changes
location = {i: String(f"location_{i}") for i in range(len(friends) + 1)}

# Initial location and time
solver.add(location[0] == "North Beach")
solver.add(meet_start["Jeffrey"] >= time_to_minutes(900))  # Start at 9:00 AM

# Constraints for each friend
for name, details in friends.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    solver.add(meet_start[name] >= start_time)
    solver.add(meet_end[name] <= end_time)
    solver.add(meet_end[name] - meet_start[name] >= min_duration)

# Constraints for travel times
for i in range(len(friends)):
    name = list(friends.keys())[i]
    next_name = list(friends.keys())[i + 1] if i + 1 < len(friends) else None
    solver.add(meet_end[name] <= meet_start[next_name] - travel_times[(friends[name]["location"], friends[next_name]["location"])])
    solver.add(location[i + 1] == friends[next_name]["location"])

# Objective: maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(meet_start[name] < meet_end[name], 1, 0) for name in friends]))

# Solve the problem
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for name in friends.keys():
        start = model[meet_start[name]].as_long()
        end = model[meet_end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")