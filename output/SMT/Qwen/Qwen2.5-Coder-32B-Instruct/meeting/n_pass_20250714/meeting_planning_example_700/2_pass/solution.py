from z3 import *

# Define the locations
locations = ["Presidio", "Pacific Heights", "Golden Gate Park", "Fisherman's Wharf",
             "Marina District", "Alamo Square", "Sunset District", "Nob Hill", "North Beach"]

# Define the travel times (in minutes)
travel_times = {
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "North Beach"): 23,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "North Beach"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Nob Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "North Beach"): 8,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Nob Hill"): 7,
}

# Define the friends' availability and meeting requirements
friends = {
    "Kevin": {"location": "Pacific Heights", "start": 7*60 + 15, "end": 8*60 + 45, "min_meeting": 90},
    "Michelle": {"location": "Golden Gate Park", "start": 20*60, "end": 21*60, "min_meeting": 15},
    "Emily": {"location": "Fisherman's Wharf", "start": 16*60 + 15, "end": 19*60, "min_meeting": 30},
    "Mark": {"location": "Marina District", "start": 18*60 + 15, "end": 19*60 + 45, "min_meeting": 75},
    "Barbara": {"location": "Alamo Square", "start": 17*60, "end": 19*60, "min_meeting": 120},
    "Laura": {"location": "Sunset District", "start": 19*60, "end": 21*15, "min_meeting": 75},
    "Mary": {"location": "Nob Hill", "start": 17*60 + 30, "end": 19*60, "min_meeting": 45},
    "Helen": {"location": "North Beach", "start": 11*60, "end": 12*15, "min_meeting": 45},
}

# Create a solver instance
solver = Solver()

# Define variables for the time spent at each location
time_at_location = {loc: Int(f"time_at_{loc}") for loc in locations}

# Define variables for the start time at each location
start_time_at_location = {loc: Int(f"start_time_at_{loc}") for loc in locations}

# Define binary variables to indicate if we meet each friend
meet_friend = {friend: Bool(f"meet_{friend}") for friend in friends}

# Initial constraints
solver.add(start_time_at_location["Presidio"] == 9*60)  # Start at Presidio at 9:00 AM

# Add constraints for each friend
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_meeting = details["min_meeting"]
    
    # Constraint to meet the friend for at least the minimum required time if we decide to meet them
    solver.add(Implies(meet_friend[friend], time_at_location[loc] >= min_meeting))
    solver.add(Implies(meet_friend[friend], start_time_at_location[loc] + time_at_location[loc] <= end))
    solver.add(Implies(meet_friend[friend], start_time_at_location[loc] >= start))
    
    # If we don't meet the friend, we spend no time there
    solver.add(Implies(Not(meet_friend[friend]), time_at_location[loc] == 0))

# Add constraints for travel times between locations
for i in range(len(locations)):
    for j in range(i + 1, len(locations)):
        loc1, loc2 = locations[i], locations[j]
        travel_time = travel_times[(loc1, loc2)]
        
        # If you leave loc1 to go to loc2, you must arrive before starting at loc2
        solver.add(start_time_at_location[loc2] >= start_time_at_location[loc1] + time_at_location[loc1] + travel_time)
        solver.add(start_time_at_location[loc1] >= start_time_at_location[loc2] + time_at_location[loc2] + travel_time)

# Constraint to meet exactly 5 people
solver.add(Sum([If(meet_friend[friend], 1, 0) for friend in friends]) == 5)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {loc: (model[start_time_at_location[loc]].as_long(), model[time_at_location[loc]].as_long()) for loc in locations}
    print("SOLUTION:")
    for loc, (start, duration) in solution.items():
        if duration > 0:
            print(f"At {loc} from {start//60}:{start%60:02d} for {duration} minutes")
else:
    print("No solution found")