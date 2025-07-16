from z3 import *
from itertools import permutations

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

# Function to check if a sequence of friends is feasible
def check_sequence(sequence):
    solver = Solver()
    
    # Define variables for the start time of each friend meeting
    meeting_start_times = {friend: Int(f"start_{friend}") for friend in sequence}
    
    # Initialize current location and time
    current_location = "Haight-Ashbury"
    current_time = 9 * 60  # Start time at Haight-Ashbury
    
    for friend in sequence:
        location = friends[friend]["location"]
        start = friends[friend]["start"]
        end = friends[friend]["end"]
        min_meeting_time = friends[friend]["min_meeting_time"]
        
        # Travel time to the friend's location
        travel_time = travel_times[(current_location, location)]
        current_time += travel_time
        
        # Meeting time with the friend
        solver.add(meeting_start_times[friend] == current_time)
        solver.add(meeting_start_times[friend] + min_meeting_time <= end)
        solver.add(meeting_start_times[friend] >= start)
        
        # Update the current location and time after meeting
        current_time += min_meeting_time
        current_location = location
    
    # Ensure the total time does not exceed the end of the day at 5:45 PM
    solver.add(current_time <= 17*60 + 45)
    
    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        return model, sequence
    else:
        return None, None

# Generate all permutations of 4 friends out of 5
all_permutations = permutations(friends.keys(), 4)

# Check each permutation
for permutation in all_permutations:
    model, valid_permutation = check_sequence(permutation)
    if model:
        print("SOLUTION:")
        for friend in valid_permutation:
            start_time = model[meeting_start_times[friend]].as_long()
            hours = start_time // 60
            minutes = start_time % 60
            print(f"Meet {friend} at {hours:02}:{minutes:02} for {friends[friend]['min_meeting_time']} minutes.")
        break
else:
    print("No solution found.")