from z3 import *

# Define the locations
locations = ["Haight-Ashbury", "Mission District", "Bayview", "Pacific Heights", "Russian Hill", "Fisherman's Wharf"]

# Define the travel times between locations
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define the friends' availability and meeting requirements
friends = {
    "Stephanie": {"location": "Mission District", "start": 8*60 + 15, "end": 13*60 + 45, "min_meeting_time": 90},
    "Sandra": {"location": "Bayview", "start": 13*60, "end": 19*60 + 30, "min_meeting_time": 15},
    "Richard": {"location": "Pacific Heights", "start": 7*60 + 15, "end": 10*60 + 15, "min_meeting_time": 75},
    "Brian": {"location": "Russian Hill", "start": 12*60 + 15, "end": 16*60, "min_meeting_time": 120},
    "Jason": {"location": "Fisherman's Wharf", "start": 8*60 + 30, "end": 17*60 + 45, "min_meeting_time": 60},
}

# Create a solver instance
solver = Solver()

# Define binary variables to indicate whether we meet each friend
meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends}

# Define variables for the start time of each friend meeting
meeting_start_times = {friend: Int(f"start_{friend}") for friend in friends}

# Add constraints for each friend
for friend, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_meeting_time = details["min_meeting_time"]
    
    # If we meet the friend, they must be met within their available time
    solver.add(Implies(meet_friends[friend], meeting_start_times[friend] >= start))
    solver.add(Implies(meet_friends[friend], meeting_start_times[friend] + min_meeting_time <= end))

# Ensure we meet exactly 4 people
solver.add(Sum([If(meet_friends[friend], 1, 0) for friend in friends]) == 4)

# Initialize current location and time
current_location = "Haight-Ashbury"
current_time = 9 * 60  # Start time at Haight-Ashbury

# List to store the sequence of meetings
meeting_sequence = []

# Add constraints for travel times and meeting sequence
for friend in friends:
    location = friends[friend]["location"]
    min_meeting_time = friends[friend]["min_meeting_time"]
    
    # If we meet the friend, update the current time and location
    travel_time = travel_times[(current_location, location)]
    next_time = current_time + travel_time + min_meeting_time
    
    # Add constraints for meeting sequence
    solver.add(Implies(meet_friends[friend], meeting_start_times[friend] == current_time + travel_time))
    solver.add(Implies(meet_friends[friend], next_time <= 17*60 + 45))  # End of the day at 5:45 PM
    
    # Update the current location and time after meeting
    current_location = location
    current_time = next_time

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in friends:
        if model.evaluate(meet_friends[friend]):
            start_time = model[meeting_start_times[friend]].as_long()
            hours = start_time // 60
            minutes = start_time % 60
            print(f"Meet {friend} at {hours:02}:{minutes:02} for {friends[friend]['min_meeting_time']} minutes.")
else:
    print("No solution found.")