from z3 import *

# Define the locations
locations = ["Fisherman's Wharf", "Bayview", "Golden Gate Park", "Nob Hill", "Marina District", "Embarcadero"]

# Define the travel times in minutes
travel_times = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
}

# Define the friends and their availability
friends = {
    "Thomas": {"location": "Bayview", "start": 15.5, "end": 18.5, "duration": 2},
    "Stephanie": {"location": "Golden Gate Park", "start": 18.5, "end": 9.75, "duration": 0.5},
    "Laura": {"location": "Nob Hill", "start": 8.75, "end": 16.25, "duration": 0.5},
    "Betty": {"location": "Marina District", "start": 18.75, "end": 9.75, "duration": 0.75},
    "Patricia": {"location": "Embarcadero", "start": 17.5, "end": 10, "duration": 0.75},
}

# Create a solver instance
solver = Solver()

# Define binary variables to indicate whether we visit each friend
visit = {friend: Bool(f"visit_{friend}") for friend in friends}

# Define variables for the start time at each location
start_time_at_location = {friend: Real(f"start_time_at_{friend}") for friend in friends}

# Define variables for the time spent at each location
time_at_location = {friend: Real(f"time_at_{friend}") for friend in friends}

# Add constraints for the number of friends visited
solver.add(Sum([If(visit[friend], 1, 0) for friend in friends]) == 5)

# Add constraints for the time spent at each location
for friend, details in friends.items():
    solver.add(Implies(visit[friend], time_at_location[friend] >= details["duration"]))
    solver.add(Implies(Not(visit[friend]), time_at_location[friend] == 0))

# Add constraints for the start time at each location
for friend, details in friends.items():
    solver.add(Implies(visit[friend], start_time_at_location[friend] + time_at_location[friend] <= details["end"]))
    solver.add(Implies(visit[friend], start_time_at_location[friend] >= details["start"]))
    solver.add(Implies(Not(visit[friend]), start_time_at_location[friend] == 0))

# Add constraints for the travel times between locations
current_location = "Fisherman's Wharf"
current_time = 9.0

# List to keep track of the order of visits
visit_order = []

for friend in friends:
    # Calculate the travel time from the current location to the friend's location
    travel_time = travel_times[(current_location, friends[friend]["location"])] / 60.0
    
    # Add constraint for the start time at the friend's location
    solver.add(Implies(visit[friend], start_time_at_location[friend] >= current_time + travel_time))
    
    # Update the current location and time
    current_location = friends[friend]["location"]
    current_time = start_time_at_location[friend] + time_at_location[friend]
    
    # Add the friend to the visit order
    visit_order.append(friend)

# Ensure that the visit order respects the constraints
for i in range(len(visit_order)):
    for j in range(i + 1, len(visit_order)):
        solver.add(Implies(And(visit[visit_order[i]], visit[visit_order[j]]), start_time_at_location[visit_order[i]] < start_time_at_location[visit_order[j]]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {}
    for friend in friends:
        if model[visit[friend]]:
            solution[friend] = {
                "start_time": model[start_time_at_location[friend]].as_decimal(2),
                "end_time": model[start_time_at_location[friend]].as_decimal(2) + model[time_at_location[friend]].as_decimal(2),
                "location": friends[friend]["location"],
                "duration": model[time_at_location[friend]].as_decimal(2)
            }
    print("SOLUTION:")
    for friend, details in solution.items():
        print(f"{friend}: Start at {details['start_time']}PM, End at {details['end_time']}PM, Location: {details['location']}, Duration: {details['duration']} hours")
else:
    print("No solution found.")