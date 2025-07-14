from z3 import *

# Define the locations
locations = [
    "Richmond District", "Chinatown", "Sunset District", "Alamo Square",
    "Financial District", "North Beach", "Embarcadero", "Presidio",
    "Golden Gate Park", "Bayview"
]

# Define the travel times (in minutes)
travel_times = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Golden Gate Park", "Bayview"): 22,
}

# Make the travel times symmetric
for (u, v), t in list(travel_times.items()):
    travel_times[(v, u)] = t

# Define the friends and their availability
friends = {
    "Robert": {"location": "Chinatown", "start": 7*60+45, "end": 17*60+30, "min_time": 120},
    "David": {"location": "Sunset District", "start": 12*60+30, "end": 19*60+45, "min_time": 45},
    "Matthew": {"location": "Alamo Square", "start": 8*60+45, "end": 1*60+45, "min_time": 90},
    "Jessica": {"location": "Financial District", "start": 9*60+30, "end": 18*60+45, "min_time": 45},
    "Melissa": {"location": "North Beach", "start": 7*60+15, "end": 16*60+45, "min_time": 45},
    "Mark": {"location": "Embarcadero", "start": 15*60+15, "end": 17*60, "min_time": 45},
    "Deborah": {"location": "Presidio", "start": 19*60, "end": 19*60+45, "min_time": 45},
    "Karen": {"location": "Golden Gate Park", "start": 19*60+30, "end": 22*60, "min_time": 120},
    "Laura": {"location": "Bayview", "start": 21*60+15, "end": 22*60+15, "min_time": 15},
}

# Create a solver instance
solver = Solver()

# Define boolean variables to indicate whether we meet each friend
meet_vars = {name: Bool(f"meet_{name}") for name in friends}

# Define variables for each friend: start time and end time
friend_vars = {name: (Int(f"{name}_start"), Int(f"{name}_end")) for name in friends}

# Add constraints for each friend
for name, data in friends.items():
    start, end = friend_vars[name]
    meet = meet_vars[name]
    solver.add(Implies(meet, start >= data["start"]))
    solver.add(Implies(meet, end <= data["end"]))
    solver.add(Implies(meet, end - start >= data["min_time"]))

# Add constraints for travel times between friends' meetings
prev_location = "Richmond District"
prev_end = 9*60  # Start at 9:00 AM

# Track the last met friend
last_met = None

for name, data in friends.items():
    start, end = friend_vars[name]
    meet = meet_vars[name]
    if last_met is not None:
        last_start, last_end = friend_vars[last_met]
        last_meet = meet_vars[last_met]
        travel_time = travel_times[(prev_location, data["location"])]
        solver.add(Implies(And(meet, last_meet), start >= last_end + travel_time))
    prev_location = data["location"]
    last_met = name

# Ensure exactly 8 friends are met
solver.add(Sum([If(meet_vars[name], 1, 0) for name in friends]) == 8)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for name, (start_var, end_var) in friend_vars.items():
        if model.evaluate(meet_vars[name]):
            start_time = model[start_var].as_long()
            end_time = model[end_var].as_long()
            schedule.append((name, start_time, end_time))
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for name, start, end in schedule:
        print(f"Meet {name} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
else:
    print("No feasible schedule found.")