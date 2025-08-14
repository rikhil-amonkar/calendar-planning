from z3 import *

# Define the locations
locations = [
    "Union Square", "Presidio", "Alamo Square", "Marina District", 
    "Financial District", "Nob Hill", "Sunset District", "Chinatown", 
    "Russian Hill", "North Beach", "Haight-Ashbury"
]

# Define the travel times as a dictionary of dictionaries
travel_times = {
    "Union Square": {"Presidio": 24, "Alamo Square": 15, "Marina District": 18, "Financial District": 9, "Nob Hill": 9, "Sunset District": 27, "Chinatown": 7, "Russian Hill": 13, "North Beach": 10, "Haight-Ashbury": 18},
    "Presidio": {"Union Square": 22, "Alamo Square": 19, "Marina District": 11, "Financial District": 23, "Nob Hill": 18, "Sunset District": 15, "Chinatown": 21, "Russian Hill": 14, "North Beach": 18, "Haight-Ashbury": 15},
    "Alamo Square": {"Union Square": 14, "Presidio": 17, "Marina District": 15, "Financial District": 17, "Nob Hill": 11, "Sunset District": 16, "Chinatown": 15, "Russian Hill": 13, "North Beach": 15, "Haight-Ashbury": 5},
    "Marina District": {"Union Square": 16, "Presidio": 10, "Alamo Square": 15, "Financial District": 17, "Nob Hill": 12, "Sunset District": 19, "Chinatown": 15, "Russian Hill": 8, "North Beach": 11, "Haight-Ashbury": 16},
    "Financial District": {"Union Square": 9, "Presidio": 22, "Alamo Square": 17, "Marina District": 15, "Nob Hill": 8, "Sunset District": 30, "Chinatown": 5, "Russian Hill": 11, "North Beach": 7, "Haight-Ashbury": 19},
    "Nob Hill": {"Union Square": 7, "Presidio": 17, "Alamo Square": 11, "Marina District": 11, "Financial District": 9, "Sunset District": 24, "Chinatown": 6, "Russian Hill": 5, "North Beach": 8, "Haight-Ashbury": 13},
    "Sunset District": {"Union Square": 30, "Presidio": 16, "Alamo Square": 17, "Marina District": 21, "Financial District": 30, "Nob Hill": 27, "Chinatown": 29, "Russian Hill": 23, "North Beach": 27, "Haight-Ashbury": 15},
    "Chinatown": {"Union Square": 7, "Presidio": 19, "Alamo Square": 17, "Marina District": 12, "Financial District": 5, "Nob Hill": 9, "Sunset District": 29, "Russian Hill": 7, "North Beach": 3, "Haight-Ashbury": 19},
    "Russian Hill": {"Union Square": 10, "Presidio": 14, "Alamo Square": 15, "Marina District": 7, "Financial District": 11, "Nob Hill": 5, "Sunset District": 23, "Chinatown": 9, "North Beach": 5, "Haight-Ashbury": 17},
    "North Beach": {"Union Square": 7, "Presidio": 17, "Alamo Square": 16, "Marina District": 9, "Financial District": 8, "Nob Hill": 7, "Sunset District": 27, "Chinatown": 6, "Russian Hill": 4, "Haight-Ashbury": 18},
    "Haight-Ashbury": {"Union Square": 19, "Presidio": 15, "Alamo Square": 5, "Marina District": 17, "Financial District": 21, "Nob Hill": 15, "Sunset District": 15, "Chinatown": 19, "Russian Hill": 17, "North Beach": 19}
}

# Define the friends and their availability
friends = {
    "Kimberly": {"location": "Presidio", "start": 1530, "end": 1600, "min_duration": 15},
    "Elizabeth": {"location": "Alamo Square", "start": 1915, "end": 2015, "min_duration": 15},
    "Joshua": {"location": "Marina District", "start": 1030, "end": 1415, "min_duration": 45},
    "Sandra": {"location": "Financial District", "start": 1930, "end": 2015, "min_duration": 45},
    "Kenneth": {"location": "Nob Hill", "start": 1245, "end": 2145, "min_duration": 30},
    "Betty": {"location": "Sunset District", "start": 1400, "end": 1900, "min_duration": 60},
    "Deborah": {"location": "Chinatown", "start": 1715, "end": 2030, "min_duration": 15},
    "Barbara": {"location": "Russian Hill", "start": 1730, "end": 2115, "min_duration": 120},
    "Steven": {"location": "North Beach", "start": 1745, "end": 2045, "min_duration": 90},
    "Daniel": {"location": "Haight-Ashbury", "start": 1830, "end": 1845, "min_duration": 15}
}

# Convert times to minutes since 9:00 AM
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return (hours - 9) * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start times of each meeting
meeting_starts = {friend: Int(f"start_{friend}") for friend in friends}
meeting_ends = {friend: Int(f"end_{friend}") for friend in friends}
meeting_vars = {friend: Bool(f"meet_{friend}") for friend in friends}

# Add constraints for each friend
for friend, details in friends.items():
    location = details["location"]
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    
    # Meeting must start within the friend's available time
    solver.add(Implies(meeting_vars[friend], meeting_starts[friend] >= start_time))
    solver.add(Implies(meeting_vars[friend], meeting_starts[friend] <= end_time - min_duration))
    
    # Meeting must not exceed the friend's available time
    solver.add(Implies(meeting_vars[friend], meeting_starts[friend] + min_duration <= end_time))
    
    # Define the end time of the meeting
    solver.add(meeting_ends[friend] == meeting_starts[friend] + min_duration)

# Define a variable for the current location
current_location = "Union Square"
current_time = 0

# Add travel constraints
for friend in sorted(friends.keys(), key=lambda x: friends[x]["start"]):
    location = friends[friend]["location"]
    if location != current_location:
        travel_time = travel_times[current_location][location]
        solver.add(Implies(meeting_vars[friend], meeting_starts[friend] >= current_time + travel_time))
        current_location = location
    current_time = meeting_ends[friend]

# Ensure exactly 7 meetings are scheduled
solver.add(Sum([If(meeting_vars[friend], 1, 0) for friend in friends]) == 7)

# Check if the solver found a solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, details in friends.items():
        if model[meeting_vars[friend]]:
            start_time = model[meeting_starts[friend]].as_long()
            hours, minutes = divmod(start_time, 60)
            print(f"Meet {friend} at {hours:02}:{minutes:02} at {details['location']}")
else:
    print("No solution found.")