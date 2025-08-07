from z3 import *

# Define the locations and their travel times
locations = ["Presidio", "Haight-Ashbury", "Nob Hill", "Russian Hill", "North Beach", "Chinatown", "Union Square", "Embarcadero", "Financial District", "Marina District"]
travel_times = {
    ("Presidio", "Haight-Ashbury"): 15, ("Presidio", "Nob Hill"): 18, ("Presidio", "Russian Hill"): 14, ("Presidio", "North Beach"): 18, ("Presidio", "Chinatown"): 21, ("Presidio", "Union Square"): 22, ("Presidio", "Embarcadero"): 20, ("Presidio", "Financial District"): 23, ("Presidio", "Marina District"): 11,
    ("Haight-Ashbury", "Presidio"): 15, ("Haight-Ashbury", "Nob Hill"): 15, ("Haight-Ashbury", "Russian Hill"): 17, ("Haight-Ashbury", "North Beach"): 19, ("Haight-Ashbury", "Chinatown"): 19, ("Haight-Ashbury", "Union Square"): 19, ("Haight-Ashbury", "Embarcadero"): 20, ("Haight-Ashbury", "Financial District"): 21, ("Haight-Ashbury", "Marina District"): 17,
    ("Nob Hill", "Presidio"): 17, ("Nob Hill", "Haight-Ashbury"): 13, ("Nob Hill", "Russian Hill"): 5, ("Nob Hill", "North Beach"): 8, ("Nob Hill", "Chinatown"): 6, ("Nob Hill", "Union Square"): 7, ("Nob Hill", "Embarcadero"): 9, ("Nob Hill", "Financial District"): 9, ("Nob Hill", "Marina District"): 11,
    ("Russian Hill", "Presidio"): 14, ("Russian Hill", "Haight-Ashbury"): 17, ("Russian Hill", "Nob Hill"): 5, ("Russian Hill", "North Beach"): 5, ("Russian Hill", "Chinatown"): 9, ("Russian Hill", "Union Square"): 10, ("Russian Hill", "Embarcadero"): 8, ("Russian Hill", "Financial District"): 11, ("Russian Hill", "Marina District"): 7,
    ("North Beach", "Presidio"): 17, ("North Beach", "Haight-Ashbury"): 18, ("North Beach", "Nob Hill"): 7, ("North Beach", "Russian Hill"): 4, ("North Beach", "Chinatown"): 6, ("North Beach", "Union Square"): 7, ("North Beach", "Embarcadero"): 6, ("North Beach", "Financial District"): 8, ("North Beach", "Marina District"): 9,
    ("Chinatown", "Presidio"): 19, ("Chinatown", "Haight-Ashbury"): 19, ("Chinatown", "Nob Hill"): 9, ("Chinatown", "Russian Hill"): 7, ("Chinatown", "North Beach"): 3, ("Chinatown", "Union Square"): 7, ("Chinatown", "Embarcadero"): 5, ("Chinatown", "Financial District"): 5, ("Chinatown", "Marina District"): 12,
    ("Union Square", "Presidio"): 24, ("Union Square", "Haight-Ashbury"): 18, ("Union Square", "Nob Hill"): 9, ("Union Square", "Russian Hill"): 13, ("Union Square", "North Beach"): 10, ("Union Square", "Chinatown"): 7, ("Union Square", "Embarcadero"): 11, ("Union Square", "Financial District"): 9, ("Union Square", "Marina District"): 18,
    ("Embarcadero", "Presidio"): 20, ("Embarcadero", "Haight-Ashbury"): 21, ("Embarcadero", "Nob Hill"): 10, ("Embarcadero", "Russian Hill"): 8, ("Embarcadero", "North Beach"): 5, ("Embarcadero", "Chinatown"): 7, ("Embarcadero", "Union Square"): 10, ("Embarcadero", "Financial District"): 5, ("Embarcadero", "Marina District"): 12,
    ("Financial District", "Presidio"): 22, ("Financial District", "Haight-Ashbury"): 19, ("Financial District", "Nob Hill"): 8, ("Financial District", "Russian Hill"): 11, ("Financial District", "North Beach"): 7, ("Financial District", "Chinatown"): 5, ("Financial District", "Union Square"): 9, ("Financial District", "Embarcadero"): 4, ("Financial District", "Marina District"): 15,
    ("Marina District", "Presidio"): 10, ("Marina District", "Haight-Ashbury"): 16, ("Marina District", "Nob Hill"): 12, ("Marina District", "Russian Hill"): 8, ("Marina District", "North Beach"): 11, ("Marina District", "Chinatown"): 15, ("Marina District", "Union Square"): 16, ("Marina District", "Embarcadero"): 14, ("Marina District", "Financial District"): 17,
}

# Define the friends and their availability
friends = {
    "Karen": {"location": "Haight-Ashbury", "start": 2100, "end": 2145, "min_duration": 45},
    "Jessica": {"location": "Nob Hill", "start": 1345, "end": 2100, "min_duration": 90},
    "Brian": {"location": "Russian Hill", "start": 1530, "end": 2145, "min_duration": 60},
    "Kenneth": {"location": "North Beach", "start": 945, "end": 2100, "min_duration": 30},
    "Jason": {"location": "Chinatown", "start": 815, "end": 1145, "min_duration": 75},
    "Stephanie": {"location": "Union Square", "start": 1445, "end": 1845, "min_duration": 105},
    "Kimberly": {"location": "Embarcadero", "start": 945, "end": 1930, "min_duration": 75},
    "Steven": {"location": "Financial District", "start": 715, "end": 2115, "min_duration": 60},
    "Mark": {"location": "Marina District", "start": 1015, "end": 1300, "min_duration": 75},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    return time // 100 * 60 + time % 100

# Create a solver instance
solver = Solver()

# Define variables for each friend's meeting start time
meeting_start = {name: Int(f"start_{name}") for name in friends}

# Define constraints
for name, details in friends.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    solver.add(meeting_start[name] >= start_time)
    solver.add(meeting_start[name] + min_duration <= end_time)

# Define the current location and start time
current_location = "Presidio"
current_time = time_to_minutes(900)  # 9:00 AM

# Define constraints for travel times
for name, details in friends.items():
    location = details["location"]
    travel_time = travel_times[(current_location, location)]
    solver.add(meeting_start[name] >= current_time + travel_time)

# Define constraints for non-overlapping meetings and travel times
for i, (name1, details1) in enumerate(friends.items()):
    for j, (name2, details2) in enumerate(friends.items()):
        if i < j:
            solver.add(Or(meeting_start[name1] + details1["min_duration"] + travel_times[(details1["location"], details2["location"])] <= meeting_start[name2],
                          meeting_start[name2] + details2["min_duration"] + travel_times[(details2["location"], details1["location"])] <= meeting_start[name1]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in friends.items():
        start_time = model[meeting_start[name]].as_long()
        end_time = start_time + details["min_duration"]
        itinerary.append({"action": "meet", "person": name, "start_time": f"{start_time // 60:02}:{start_time % 60:02}", "end_time": f"{end_time // 60:02}:{end_time % 60:02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")