from z3 import *

# Define the locations
locations = [
    "Bayview", "North Beach", "Fisherman's Wharf", "Haight-Ashbury",
    "Nob Hill", "Golden Gate Park", "Union Square", "Alamo Square",
    "Presidio", "Chinatown", "Pacific Heights"
]

# Define the travel times in minutes
travel_times = {
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Chinatown"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
}

# Define the friends' availability
friends_availability = {
    "Brian": {"location": "North Beach", "start": 13 * 60, "end": 19 * 60, "min_duration": 90},
    "Richard": {"location": "Fisherman's Wharf", "start": 11 * 60, "end": 12 * 45, "min_duration": 60},
    "Ashley": {"location": "Haight-Ashbury", "start": 15 * 60, "end": 20 * 30, "min_duration": 90},
    "Elizabeth": {"location": "Nob Hill", "start": 11 * 45, "end": 18 * 30, "min_duration": 75},
    "Jessica": {"location": "Golden Gate Park", "start": 20 * 0, "end": 21 * 45, "min_duration": 105},
    "Deborah": {"location": "Union Square", "start": 17 * 30, "end": 22 * 0, "min_duration": 60},
    "Kimberly": {"location": "Alamo Square", "start": 17 * 30, "end": 21 * 15, "min_duration": 45},
    "Matthew": {"location": "Presidio", "start": 8 * 15, "end": 9 * 0, "min_duration": 15},
    "Kenneth": {"location": "Chinatown", "start": 13 * 45, "end": 19 * 30, "min_duration": 105},
    "Anthony": {"location": "Pacific Heights", "start": 14 * 15, "end": 16 * 0, "min_duration": 30},
}

# Create a Z3 solver instance
solver = Solver()

# Define variables
current_location = "Bayview"
current_time = 9 * 60

# Define variables for each friend
friend_meetings = {}
meeting_order = []

# Add constraints for each friend
for friend, availability in friends_availability.items():
    # Define variables for meeting start and end times
    meet_start = Int(friend + "_meet_start")
    meet_end = Int(friend + "_meet_end")
    
    # Constraints for meeting duration
    solver.add(meet_end - meet_start >= availability["min_duration"])
    
    # Constraints for meeting within available time
    solver.add(meet_start >= availability["start"])
    solver.add(meet_end <= availability["end"])
    
    # Constraints for traveling to and from the meeting
    travel_to_meeting = Int(friend + "_travel_to_meeting")
    travel_from_meeting = Int(friend + "_travel_from_meeting")
    
    solver.add(travel_to_meeting == If(friend_meetings.get(friend, False), travel_times[(current_location, availability["location"])], 0))
    solver.add(travel_from_meeting == If(friend_meetings.get(friend, False), travel_times[(availability["location"], current_location)], 0))
    
    # Update current time after meeting
    solver.add(current_time + travel_to_meeting <= meet_start)
    solver.add(current_time + travel_to_meeting + meet_end - meet_start + travel_from_meeting <= 24 * 60)
    
    # Ensure that if a friend is met, the meeting starts after the previous activity
    solver.add(Implies(friend_meetings.get(friend, False), meet_start >= current_time + travel_to_meeting))
    
    # Update current location after meeting
    solver.add(Implies(friend_meetings.get(friend, False), current_location == availability["location"]))
    
    # Add to meeting order
    meeting_order.append((friend, meet_start, meet_end))
    
    # Add boolean variable for meeting
    friend_meetings[friend] = Bool(friend + "_met")

# Ensure exactly 8 friends are met
solver.add(Sum([If(friend_meetings[friend], 1, 0) for friend in friends_availability]) == 8)

# Solve the problem
result = solver.check()

# Print the solution
if result == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, meet_start, meet_end in meeting_order:
        if model.evaluate(friend_meetings[friend]):
            start_time = model.evaluate(meet_start).as_long()
            end_time = model.evaluate(meet_end).as_long()
            print(f"Meet {friend} from {start_time // 60}:{start_time % 60:02d} to {end_time // 60}:{end_time % 60:02d}")
else:
    print("No solution found.")