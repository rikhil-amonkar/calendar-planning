from z3 import *

# Define the time slots in minutes from 9:00 AM to 9:00 PM
time_slots = list(range(540, 1260))  # 540 minutes is 9:00 AM, 1260 minutes is 9:00 PM

# Define the locations
locations = ["Marina District", "Bayview", "Sunset District", "Richmond District",
             "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach", "Russian Hill", "Embarcadero"]

# Define the travel times between locations
travel_times = {
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Embarcadero"): 14,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Embarcadero"): 19,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Embarcadero"): 30,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Embarcadero"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Embarcadero"): 6,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Russian Hill"): 8,
}

# Define the availability and meeting duration requirements for each friend
friends = {
    "Charles": {"location": "Bayview", "start": 690, "end": 1410, "duration": 45},  # 11:30 AM to 2:30 PM
    "Robert": {"location": "Sunset District", "start": 1125, "end": 1260, "duration": 30},  # 4:45 PM to 9:00 PM
    "Karen": {"location": "Richmond District", "start": 1275, "end": 1350, "duration": 60},  # 7:15 PM to 9:30 PM
    "Rebecca": {"location": "Nob Hill", "start": 1155, "end": 1470, "duration": 90},  # 4:15 PM to 8:30 PM
    "Margaret": {"location": "Chinatown", "start": 855, "end": 1305, "duration": 120},  # 2:15 PM to 7:45 PM
    "Patricia": {"location": "Haight-Ashbury", "start": 870, "end": 1470, "duration": 45},  # 2:30 PM to 8:30 PM
    "Mark": {"location": "North Beach", "start": 840, "end": 1290, "duration": 105},  # 2:00 PM to 6:30 PM
    "Melissa": {"location": "Russian Hill", "start": 780, "end": 1305, "duration": 30},  # 1:00 PM to 7:45 PM
    "Laura": {"location": "Embarcadero", "start": 540, "end": 795, "duration": 105},  # 7:45 AM to 1:15 PM
}

# Create a solver instance
solver = Solver()

# Define variables for each friend indicating if they are met
met_friends = {friend: Bool(f'met_{friend}') for friend in friends}

# Define variables for the location and time slot for each friend meeting
meeting_location = {friend: Int(f'location_{friend}') for friend in friends}
meeting_time = {friend: Int(f'time_{friend}') for friend in friends}

# Add constraints for each friend
for friend, info in friends.items():
    # Friend must be met within their availability window
    solver.add(meeting_time[friend] >= info["start"])
    solver.add(meeting_time[friend] + info["duration"] <= info["end"])
    
    # Friend must be met at their location
    solver.add(meeting_location[friend] == locations.index(info["location"]))
    
    # If a friend is met, then their meeting time and location must be valid
    solver.add(Implies(met_friends[friend], And(
        meeting_time[friend] >= info["start"],
        meeting_time[friend] + info["duration"] <= info["end"],
        meeting_location[friend] == locations.index(info["location"])
    )))

# Add constraints for travel times between meetings
for i in range(len(friends) - 1):
    friend1 = list(friends.keys())[i]
    friend2 = list(friends.keys())[i + 1]
    solver.add(Implies(And(met_friends[friend1], met_friends[friend2]), 
                       meeting_time[friend1] + friends[friend1]["duration"] + travel_times[(locations[meeting_location[friend1]], locations[meeting_location[friend2]])] <= meeting_time[friend2]))

# Add constraint to start at Marina District at 9:00 AM
initial_location = locations.index("Marina District")
initial_time = 540
if len(friends) > 0:
    first_friend = list(friends.keys())[0]
    solver.add(Implies(met_friends[first_friend], And(
        meeting_time[first_friend] >= initial_time + travel_times[(locations[initial_location], locations[meeting_location[first_friend]])],
        meeting_location[first_friend] != initial_location
    )))

# Ensure exactly 8 friends are met
solver.add(Sum([If(met_friends[friend], 1, 0) for friend in friends]) == 8)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in friends:
        if model.evaluate(met_friends[friend]):
            loc = model.evaluate(meeting_location[friend])
            time_start = model.evaluate(meeting_time[friend])
            time_end = time_start + friends[friend]["duration"]
            print(f"Meet {friend} at {locations[loc.as_long()]} from {time_start // 60}:{time_start % 60:02d} to {time_end // 60}:{time_end % 60:02d}")
else:
    print("No solution found.")