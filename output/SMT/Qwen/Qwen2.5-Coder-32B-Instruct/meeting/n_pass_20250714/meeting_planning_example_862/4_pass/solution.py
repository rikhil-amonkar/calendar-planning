from z3 import *

# Define the locations
locations = ["Mission District", "Alamo Square", "Presidio", "Russian Hill", "North Beach",
             "Golden Gate Park", "Richmond District", "Embarcadero", "Financial District", "Marina District"]

# Define the travel times as a dictionary
travel_times = {
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Marina District"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Marina District"): 16,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Marina District"): 9,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
}

# Define the friends' availability and meeting duration requirements
friends = {
    "Laura": {"location": "Alamo Square", "start": 14*60 + 30, "end": 16*60 + 15, "duration": 75},
    "Brian": {"location": "Presidio", "start": 10*60 + 15, "end": 17*60, "duration": 30},
    "Karen": {"location": "Russian Hill", "start": 18*60, "end": 20*60 + 15, "duration": 90},
    "Stephanie": {"location": "North Beach", "start": 10*60 + 15, "end": 16*60, "duration": 75},
    "Helen": {"location": "Golden Gate Park", "start": 11*60 + 30, "end": 21*60 + 45, "duration": 120},
    "Sandra": {"location": "Richmond District", "start": 8*60, "end": 15*60 + 15, "duration": 30},
    "Mary": {"location": "Embarcadero", "start": 16*60 + 45, "end": 18*60 + 45, "duration": 120},
    "Deborah": {"location": "Financial District", "start": 19*60, "end": 20*60 + 45, "duration": 105},
    "Elizabeth": {"location": "Marina District", "start": 8*60 + 30, "end": 13*60 + 15, "duration": 105},
}

# Create a solver instance
solver = Solver()

# Define binary variables to indicate whether we meet each friend
meet_friend = {friend: Bool(f"meet_{friend}") for friend in friends}

# Define variables for the start time of meeting each friend
start_time = {friend: Int(f"start_time_{friend}") for friend in friends}

# Define a variable for the current time
current_time = Int("current_time")

# Initial time is 9:00 AM (540 minutes)
solver.add(current_time == 540)

# Add constraints for each friend
for friend, info in friends.items():
    # If we meet the friend, the start time must be within the friend's availability
    solver.add(Implies(meet_friend[friend], start_time[friend] >= info["start"]))
    solver.add(Implies(meet_friend[friend], start_time[friend] <= info["end"] - info["duration"]))
    
    # If we meet the friend, update the current time after meeting
    solver.add(Implies(meet_friend[friend], current_time == start_time[friend] + info["duration"]))

# Ensure we meet exactly 7 people
solver.add(Sum([If(meet_friend[friend], 1, 0) for friend in friends]) == 7)

# Add constraints for traveling between locations and meeting friends
previous_location = "Mission District"
previous_end_time = 540

# Create a list to store the order of meetings
meeting_order = []

for friend, info in friends.items():
    meeting_order.append((friend, info))

# Sort the meetings by start time to ensure a feasible order
meeting_order.sort(key=lambda x: x[1]["start"])

# Add constraints for the sequence of meetings
for i in range(len(meeting_order)):
    friend1, info1 = meeting_order[i]
    if i > 0:
        friend0, info0 = meeting_order[i-1]
        travel_time = travel_times[(info0["location"], info1["location"])]
        solver.add(Implies(And(meet_friend[friend0], meet_friend[friend1]), 
                           start_time[friend1] >= start_time[friend0] + info0["duration"] + travel_time))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, info in friends.items():
        if model.evaluate(meet_friend[friend]):
            print(f"Meet {friend} at {model[start_time[friend]]} for {info['duration']} minutes.")
else:
    print("No solution found.")