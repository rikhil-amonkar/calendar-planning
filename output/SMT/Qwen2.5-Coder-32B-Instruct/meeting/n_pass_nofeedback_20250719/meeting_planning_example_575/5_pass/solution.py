from z3 import *

# Define the locations
locations = ["The Castro", "Presidio", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park", "Russian Hill"]

# Define the travel times in minutes
travel_times = {
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Russian Hill"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21,
}

# Define the friends and their availability
friends = {
    "Rebecca": {"location": "Presidio", "start": 1815, "end": 2045, "duration": 60},
    "Linda": {"location": "Sunset District", "start": 1530, "end": 1945, "duration": 30},
    "Elizabeth": {"location": "Haight-Ashbury", "start": 1715, "end": 1930, "duration": 105},
    "William": {"location": "Mission District", "start": 1315, "end": 1930, "duration": 30},
    "Robert": {"location": "Golden Gate Park", "start": 1415, "end": 2130, "duration": 45},
    "Mark": {"location": "Russian Hill", "start": 1000, "end": 2115, "duration": 75},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver
solver = Solver()

# Define variables for the start time of each meeting
meeting_starts = {name: Int(f"start_{name}") for name in friends}

# Define the constraints
for name, details in friends.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    duration = details["duration"]
    solver.add(meeting_starts[name] >= start_time)
    solver.add(meeting_starts[name] + duration <= end_time)

# Define the travel constraints
current_location = "The Castro"
current_time = time_to_minutes(900)  # 9:00 AM

# Define a sequence of visits
visits = list(friends.keys())
n = len(visits)

# Define variables for the order of visits
order = [Int(f"order_{i}") for i in range(n)]

# Ensure each friend is visited exactly once
solver.add(Distinct(order))
solver.add(And([order[i] >= 0 for i in range(n)]))
solver.add(And([order[i] < n for i in range(n)]))

# Define the constraints for the sequence of visits
for i in range(n):
    if i == 0:
        prev_location = current_location
        prev_time = current_time
    else:
        prev_index = model[order[i-1]].as_long()
        prev_location = friends[visits[prev_index]]["location"]
        prev_time = meeting_starts[visits[prev_index]] + friends[visits[prev_index]]["duration"]
    
    current_index = order[i]
    current_location = friends[visits[model[current_index].as_long()]]["location"]
    travel_time = travel_times[(prev_location, current_location)]
    solver.add(meeting_starts[visits[model[current_index].as_long()]] >= prev_time + travel_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(n):
        index = model[order[i]].as_long()
        name = visits[index]
        start_time = model[meeting_starts[name]].as_long()
        end_time = start_time + friends[name]["duration"]
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")