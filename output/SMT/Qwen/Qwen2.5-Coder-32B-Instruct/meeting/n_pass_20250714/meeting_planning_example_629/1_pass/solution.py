from z3 import *

# Define the locations
locations = ["Russian Hill", "Presidio", "Chinatown", "Pacific Heights", "Richmond District", 
             "Fisherman's Wharf", "Golden Gate Park", "Bayview"]

# Define the travel times between locations
travel_times = {
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 26,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
}

# Define the availability and meeting duration requirements
availability = {
    "Matthew": {"location": "Presidio", "start": 11*60, "end": 21*60, "min_duration": 90},
    "Margaret": {"location": "Chinatown", "start": 9*60 + 15, "end": 18*60 + 45, "min_duration": 90},
    "Nancy": {"location": "Pacific Heights", "start": 14*60 + 15, "end": 17*60, "min_duration": 15},
    "Helen": {"location": "Richmond District", "start": 19*60 + 45, "end": 22*60, "min_duration": 60},
    "Rebecca": {"location": "Fisherman's Wharf", "start": 21*60 + 15, "end": 22*60 + 15, "min_duration": 60},
    "Kimberly": {"location": "Golden Gate Park", "start": 13*60, "end": 16*60 + 30, "min_duration": 120},
    "Kenneth": {"location": "Bayview", "start": 14*60 + 30, "end": 18*60, "min_duration": 60},
}

# Create a solver instance
solver = Solver()

# Define the time spent at each location
time_spent = {name: Int(name) for name in availability}

# Define the arrival time at each location
arrival_time = {loc: Int(f"arrival_{loc}") for loc in locations}

# Initial arrival time at Russian Hill
solver.add(arrival_time["Russian Hill"] == 9*60)

# Constraints for meeting each friend
for name, info in availability.items():
    loc = info["location"]
    start = info["start"]
    end = info["end"]
    min_duration = info["min_duration"]
    
    # Arrival time at the location must be within the friend's availability
    solver.add(arrival_time[loc] >= start)
    solver.add(arrival_time[loc] + time_spent[name] <= end)
    
    # Minimum duration constraint
    solver.add(time_spent[name] >= min_duration)

# Constraints for travel times
for i in range(len(locations) - 1):
    loc1 = locations[i]
    loc2 = locations[i + 1]
    solver.add(arrival_time[loc2] == arrival_time[loc1] + time_spent[loc1] + travel_times[(loc1, loc2)])

# Objective: Maximize the number of friends met
num_friends_met = Sum([If(time_spent[name] > 0, 1, 0) for name in availability])
solver.maximize(num_friends_met)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {}
    for loc in locations:
        solution[loc] = model.evaluate(arrival_time[loc]).as_long()
    for name in availability:
        solution[name] = model.evaluate(time_spent[name]).as_long()
    print("SOLUTION:")
    print(solution)
else:
    print("No solution found")