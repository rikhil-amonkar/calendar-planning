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

# Define integer variables for the order of meetings
order = {name: Int(name + "_order") for name in friends}

# Ensure each friend is met exactly once
solver.add(Distinct([order[name] for name in friends]))

# Ensure the order is between 0 and 2 (inclusive)
for name in friends:
    solver.add(order[name] >= 0)
    solver.add(order[name] <= 2)

# Define the current location and time
current_location = "The Castro"
current_time = 9.0  # 9:00 AM

# Add constraints for the sequence of meetings
for i in range(len(friends)):
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If name1 comes before name2, ensure the travel time and meeting constraints are respected
                solver.add(Implies(order[name1] < order[name2],
                                   meeting_start[name2] >= meeting_end[name1] + travel_times[(current_location, friends[name1]["location"])]/60))
                # Update the current location after the meeting
                current_location = friends[name1]["location"]

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_start[name]].as_decimal(2)
        end = model[meeting_end[name]].as_decimal(2)
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
        })
    # Sort the itinerary based on start time
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")