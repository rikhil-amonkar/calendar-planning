from z3 import *

# Define the locations
locations = ["Marina District", "Embarcadero", "Bayview", "Union Square", "Chinatown",
             "Sunset District", "Golden Gate Park", "Financial District", "Haight-Ashbury", "Mission District"]

# Define travel times as a dictionary
travel_times = {
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
}

# Define the friends and their availability
friends = {
    "Joshua": {"location": "Embarcadero", "start": 9.75, "end": 18.0, "min_meeting_time": 105},
    "Jeffrey": {"location": "Bayview", "start": 9.75, "end": 20.25, "min_meeting_time": 75},
    "Charles": {"location": "Union Square", "start": 10.75, "end": 20.25, "min_meeting_time": 120},
    "Joseph": {"location": "Chinatown", "start": 7.0, "end": 15.5, "min_meeting_time": 60},
    "Elizabeth": {"location": "Sunset District", "start": 9.0, "end": 9.75, "min_meeting_time": 45},
    "Matthew": {"location": "Golden Gate Park", "start": 11.0, "end": 19.5, "min_meeting_time": 45},
    "Carol": {"location": "Financial District", "start": 10.75, "end": 11.25, "min_meeting_time": 15},
    "Paul": {"location": "Haight-Ashbury", "start": 19.25, "end": 20.5, "min_meeting_time": 15},
    "Rebecca": {"location": "Mission District", "start": 17.0, "end": 21.75, "min_meeting_time": 45},
}

# Create a Z3 solver instance
solver = Solver()

# Define variables for the schedule
visit_times = {friend: Real(friend + "_time") for friend in friends}
current_location = "Marina District"
start_time = 9.0  # Starting at 9:00 AM

# List to keep track of visited friends
visited_friends = []

# Function to add constraints for a friend
def add_friend_constraints(friend, start_time):
    loc = friends[friend]["location"]
    start = friends[friend]["start"]
    end = friends[friend]["end"]
    min_meeting_time = friends[friend]["min_meeting_time"] / 60  # Convert minutes to hours
    
    # Ensure meeting time is within the friend's availability
    solver.add(visit_times[friend] >= start)
    solver.add(visit_times[friend] <= end - min_meeting_time)
    
    # Ensure travel time is respected
    travel_time = travel_times[(current_location, loc)] / 60  # Convert minutes to hours
    solver.add(visit_times[friend] >= start_time + travel_time)
    
    # Update current location and start time
    return loc, visit_times[friend] + min_meeting_time

# Add constraints for each friend
for friend in friends:
    if len(visited_friends) == 8:
        break
    if len(visited_friends) == 0:
        current_location, start_time = add_friend_constraints(friend, start_time)
        visited_friends.append(friend)
    else:
        # Check if we can add another friend within the day
        new_loc, new_start_time = add_friend_constraints(friend, start_time)
        if new_start_time <= 24.0:
            current_location = new_loc
            start_time = new_start_time
            visited_friends.append(friend)
        else:
            # If adding this friend exceeds 24 hours, skip this friend
            continue

# Ensure we meet exactly 8 people
assert len(visited_friends) == 8, "Could not find a schedule that meets exactly 8 people."

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in visited_friends:
        print(f"Meet {friend} at {model[visit_times[friend]]:.2f} hours after 9:00 AM")
else:
    print("No solution found.")