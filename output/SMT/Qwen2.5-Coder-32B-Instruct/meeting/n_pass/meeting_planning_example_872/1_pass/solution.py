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

# Convert times to minutes from 00:00
def time_to_minutes(time):
    return int(str(time)[:2]) * 60 + int(str(time)[2:])

# Create a solver instance
solver = Solver()

# Define variables for each friend's meeting start time
meeting_start = {name: Int(f"start_{name}") for name in friends}

# Define constraints
for name, details in friends.items():
    start = meeting_start[name]
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(start + details["min_duration"] <= time_to_minutes(details["end"]))

# Add travel constraints
for i in range(len(friends) - 1):
    name1, name2 = list(friends.keys())[i], list(friends.keys())[i + 1]
    loc1, loc2 = friends[name1]["location"], friends[name2]["location"]
    travel_time = travel_times[(loc1, loc2)]
    solver.add(meeting_start[name2] >= meeting_start[name1] + friends[name1]["min_duration"] + travel_time)

# Add the constraint for the first meeting to start at 9:00 AM
solver.add(meeting_start[list(friends.keys())[0]] >= time_to_minutes(900))

# Function to convert minutes back to HH:MM format
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes}"