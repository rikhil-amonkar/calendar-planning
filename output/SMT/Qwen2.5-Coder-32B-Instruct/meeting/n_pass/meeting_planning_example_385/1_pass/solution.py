from z3 import *

# Define the locations and their travel times
locations = ["Nob Hill", "Presidio", "North Beach", "Fisherman's Wharf", "Pacific Heights"]
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 17,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Define the friends and their availability
friends = {
    "Jeffrey": {"location": "Presidio", "start": 8*60, "end": 10*60, "min_duration": 105},
    "Steven": {"location": "North Beach", "start": 13*60 + 30, "end": 22*60, "min_duration": 45},
    "Barbara": {"location": "Fisherman's Wharf", "start": 18*60, "end": 21*30, "min_duration": 30},
    "John": {"location": "Pacific Heights", "start": 9*60, "end": 13*30, "min_duration": 15},
}

# Create a solver instance
solver = Solver()

# Define the variables
current_location = String('current_location')
current_time = Int('current_time')
meetings = {name: Bool(name) for name in friends}

# Initial conditions
solver.add(current_location == "Nob Hill")
solver.add(current_time == 9*60)

# Define the constraints for each friend
for name, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    meet = meetings[name]
    
    # If we meet the friend, we must be at their location within their availability
    solver.add(Implies(meet, current_location == location))
    solver.add(Implies(meet, current_time + min_duration <= end))
    solver.add(Implies(meet, current_time >= start))
    
    # If we meet the friend, we must have enough time to travel to their location
    for prev_location in locations:
        if prev_location != location:
            travel_time = travel_times[(prev_location, location)]
            solver.add(Implies(meet, current_time - travel_time >= 9*60))
            solver.add(Implies(meet, current_time + min_duration + travel_time <= 24*60))

# Define the objective: maximize the number of meetings
objective = Sum([If(meetings[name], 1, 0) for name in friends])

# Solve the problem
solver.maximize(objective)
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, meet in meetings.items():
        if model.evaluate(meet):
            details = friends[name]
            location = details["location"]
            start = details["start"]
            min_duration = details["min_duration"]
            # Calculate the actual start time considering travel time
            for prev_location in locations:
                if prev_location != location:
                    travel_time = travel_times[(prev_location, location)]
                    if model.evaluate(current_location == prev_location):
                        start_time = start - travel_time
                        break
            end_time = start_time + min_duration
            itinerary.append({"action": "meet", "person": name, "start_time": f"{start_time//60:02}:{start_time%60:02}", "end_time": f"{end_time//60:02}:{end_time%60:02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")