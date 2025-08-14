from z3 import *

# Define the locations and their travel times
locations = ["The Castro", "Alamo Square", "Union Square", "Chinatown"]
travel_times = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Chinatown"): 16,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Union Square"): 7,
}

# Define the friends and their availability
friends = {
    "Emily": {"location": "Alamo Square", "start": 11.75, "end": 15.25, "min_duration": 105/60},
    "Barbara": {"location": "Union Square", "start": 16.75, "end": 18.25, "min_duration": 60/60},
    "William": {"location": "Chinatown", "start": 17.25, "end": 19.0, "min_duration": 105/60},
}

# Define the solver
solver = Solver()

# Define the variables for the start and end times of each meeting
meeting_start = {name: Real(name + "_start") for name in friends}
meeting_end = {name: Real(name + "_end") for name in friends}

# Define the constraints
for name, details in friends.items():
    # Meeting must start after the person is available
    solver.add(meeting_start[name] >= details["start"])
    # Meeting must end before the person is unavailable
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])

# Define the travel constraints
current_location = "The Castro"
current_time = 9.0  # 9:00 AM

# Define the order of meetings
order_vars = {name: Int(name + "_order") for name in friends}
solver.add(Distinct([order_vars[name] for name in friends]))

# Ensure the order is sequential
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            solver.add(order_vars[name1] < order_vars[name2])

# Add travel time constraints based on the order
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            travel_time = travel_times[(friends[name1]["location"], friends[name2]["location"])]
            solver.add(meeting_start[name2] >= meeting_end[name1] + travel_time/60)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in sorted(friends, key=lambda name: model[order_vars[name]].as_long()):
        start = model[meeting_start[name]].as_decimal(2)
        end = model[meeting_end[name]].as_decimal(2)
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")