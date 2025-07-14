from z3 import *

# Define the locations
locations = [
    "Mission District", "The Castro", "Nob Hill", "Presidio",
    "Marina District", "Pacific Heights", "Golden Gate Park",
    "Chinatown", "Richmond District"
]

# Define the travel times as a dictionary
travel_times = {
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    # Add reverse paths
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# Define the friends' availability
friends_availability = {
    "Lisa": {"location": "The Castro", "start": 19*60 + 15, "end": 21*60 + 15, "duration": 120},
    "Daniel": {"location": "Nob Hill", "start": 8*60 + 15, "end": 11*60, "duration": 15},
    "Elizabeth": {"location": "Presidio", "start": 21*60 + 15, "end": 22*60 + 15, "duration": 45},
    "Steven": {"location": "Marina District", "start": 16*60 + 30, "end": 20*60 + 45, "duration": 90},
    "Timothy": {"location": "Pacific Heights", "start": 12*60, "end": 18*60, "duration": 90},
    "Ashley": {"location": "Golden Gate Park", "start": 20*60 + 45, "end": 21*60 + 45, "duration": 60},
    "Kevin": {"location": "Chinatown", "start": 12*60, "end": 19*60, "duration": 30},
    "Betty": {"location": "Richmond District", "start": 13*60 + 15, "end": 15*60 + 45, "duration": 30},
}

# Create a solver instance
solver = Solver()

# Define the decision variables
arrival_times = {friend: Int(f"arrival_{friend}") for friend in friends_availability}
departure_times = {friend: Int(f"departure_{friend}") for friend in friends_availability}
meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends_availability}

# Define the constraints
for friend, info in friends_availability.items():
    location = info["location"]
    start = info["start"]
    end = info["end"]
    duration = info["duration"]

    # Arrival time must be after the start time and before the end time minus duration
    solver.add(Implies(meet_friends[friend], arrival_times[friend] >= start))
    solver.add(Implies(meet_friends[friend], arrival_times[friend] <= end - duration))

    # Departure time is arrival time plus duration
    solver.add(Implies(meet_friends[friend], departure_times[friend] == arrival_times[friend] + duration))

    # Ensure we are at the correct location when meeting the friend
    if friend != "Daniel":  # Daniel is the first meeting
        previous_friend = [f for f in friends_availability if f != friend][0]
        solver.add(Implies(And(meet_friends[friend], meet_friends[previous_friend]),
                           departure_times[previous_friend] + travel_times[(friends_availability[previous_friend]["location"], location)] <= arrival_times[friend]))

# Start time at Mission District
solver.add(arrival_times["Daniel"] >= 9*60)

# Exactly 6 friends must be met
solver.add(Sum([If(meet_friends[friend], 1, 0) for friend in friends_availability]) == 6)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    schedule = [(friend, model[arrival_times[friend]].as_long(), model[departure_times[friend]].as_long()) for friend in friends_availability if model[meet_friends[friend]]]
    schedule.sort(key=lambda x: x[1])  # Sort by arrival time

    print("SOLUTION:")
    for friend, arrival, departure in schedule:
        print(f"{friend}: {arrival // 60}:{arrival % 60:02} - {departure // 60}:{departure % 60:02}")
else:
    print("No solution found")