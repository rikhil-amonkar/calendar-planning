from z3 import *

# Define the locations and their indices
locations = {
    "Union Square": 0,
    "Russian Hill": 1,
    "Alamo Square": 2,
    "Haight-Ashbury": 3,
    "Marina District": 4,
    "Bayview": 5,
    "Chinatown": 6,
    "Presidio": 7,
    "Sunset District": 8
}

# Define travel times in minutes
travel_times = [
    [0, 13, 15, 18, 18, 15, 7, 24, 27],
    [10, 0, 15, 17, 7, 23, 9, 14, 23],
    [14, 13, 0, 5, 15, 16, 15, 17, 16],
    [19, 17, 5, 0, 17, 18, 19, 15, 15],
    [16, 8, 15, 16, 0, 27, 15, 10, 19],
    [18, 23, 16, 19, 27, 0, 19, 32, 23],
    [7, 7, 17, 19, 12, 20, 0, 19, 29],
    [22, 14, 19, 15, 11, 31, 21, 0, 15],
    [30, 24, 17, 15, 21, 22, 30, 16, 0]
]

# Define the friends and their availability
friends = {
    "Betty": {"location": "Russian Hill", "start": 7*60, "end": 16*60 + 45, "min_duration": 105},
    "Melissa": {"location": "Alamo Square", "start": 9*60 + 30, "end": 17*60 + 15, "min_duration": 105},
    "Joshua": {"location": "Haight-Ashbury", "start": 12*60 + 15, "end": 19*60, "min_duration": 90},
    "Jeffrey": {"location": "Marina District", "start": 12*60 + 15, "end": 18*60, "min_duration": 45},
    "James": {"location": "Bayview", "start": 7*60 + 30, "end": 20*60, "min_duration": 90},
    "Anthony": {"location": "Chinatown", "start": 11*60 + 45, "end": 13*60 + 30, "min_duration": 75},
    "Timothy": {"location": "Presidio", "start": 12*60 + 30, "end": 14*60 + 45, "min_duration": 90},
    "Emily": {"location": "Sunset District", "start": 19*60 + 30, "end": 21*60 + 30, "min_duration": 120}
}

# Create a solver instance
solver = Solver()

# Define start time variables for each friend's meeting
meeting_start_times = {friend: Int(f"{friend}_start") for friend in friends}

# Add constraints for each friend
for friend, details in friends.items():
    loc_idx = locations[details["location"]]
    start_time = meeting_start_times[friend]
    
    # Friend must be available during the meeting
    solver.add(start_time >= details["start"])
    solver.add(start_time + details["min_duration"] <= details["end"])
    
    # If meeting another friend, ensure there's enough time to travel between meetings
    for other_friend, other_details in friends.items():
        if friend != other_friend:
            other_loc_idx = locations[other_details["location"]]
            other_start_time = meeting_start_times[other_friend]
            
            # Ensure no overlap in meetings
            solver.add(Or(start_time + details["min_duration"] <= other_start_time,
                          other_start_time + other_details["min_duration"] <= start_time))
            
            # Ensure enough time to travel between meetings
            solver.add(Or(start_time + details["min_duration"] + travel_times[loc_idx][other_loc_idx] <= other_start_time,
                          other_start_time + other_details["min_duration"] + travel_times[other_loc_idx][loc_idx] <= start_time))

# Start at Union Square at 9:00 AM
solver.add(meeting_start_times["Anthony"] >= 9*60)  # Anthony's earliest meeting is the latest start time

# Maximize the number of friends met
num_friends_met = Int("num_friends_met")
solver.add(num_friends_met == Sum([If(solver.model()[start_time] >= 0, 1, 0) for start_time in meeting_start_times.values()]))
solver.maximize(num_friends_met)

# Check if the problem is solvable and get the model
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, start_time in meeting_start_times.items():
        start_minute = model[start_time].as_long()
        start_hour = start_minute // 60
        start_minute %= 60
        end_minute = start_minute + friends[friend]["min_duration"]
        end_hour = end_minute // 60
        end_minute %= 60
        print(f"Meet {friend} at {start_hour:02}:{start_minute:02} for {friends[friend]['min_duration']} minutes until {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")