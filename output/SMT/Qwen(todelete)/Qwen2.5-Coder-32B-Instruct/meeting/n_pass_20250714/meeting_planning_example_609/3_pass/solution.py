from z3 import *

# Define the locations
locations = ["Chinatown", "Mission District", "Alamo Square", "Pacific Heights",
             "Union Square", "Golden Gate Park", "Sunset District", "Presidio"]

# Define the travel times between locations
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Define the friends' availability and meeting requirements
friends = {
    "David": {"location": "Mission District", "start": 8 * 60, "end": 7 * 60 + 45, "duration": 45},
    "Kenneth": {"location": "Alamo Square", "start": 14 * 60, "end": 7 * 60 + 45, "duration": 120},
    "John": {"location": "Pacific Heights", "start": 17 * 60, "end": 20 * 60, "duration": 15},
    "Charles": {"location": "Union Square", "start": 21 * 60 + 45, "end": 22 * 60 + 45, "duration": 60},
    "Deborah": {"location": "Golden Gate Park", "start": 7 * 60, "end": 18 * 60 + 15, "duration": 90},
    "Karen": {"location": "Sunset District", "start": 17 * 60 + 45, "end": 21 * 60 + 15, "duration": 15},
    "Carol": {"location": "Presidio", "start": 8 * 60 + 15, "end": 9 * 60 + 15, "duration": 30},
}

# Create a solver instance
solver = Solver()

# Define binary variables for each friend's meeting
meet_vars = {friend: Bool(f"meet_{friend}") for friend in friends}

# Define integer variables for each friend's meeting start time
meeting_start_times = {friend: Int(f"start_{friend}") for friend in friends}

# Define constraints for meeting each friend
current_location = "Chinatown"
current_time = 9 * 60  # Starting at 9:00 AM

# Ensure exactly 6 friends are met
solver.add(Sum([If(meet_vars[friend], 1, 0) for friend in friends]) == 6)

# List to store the order of meetings
meeting_order = []

for i, friend in enumerate(friends.keys()):
    # Meeting must start within the friend's availability if we decide to meet them
    solver.add(Implies(meet_vars[friend], meeting_start_times[friend] >= friends[friend]["start"]))
    solver.add(Implies(meet_vars[friend], meeting_start_times[friend] <= friends[friend]["end"] - friends[friend]["duration"]))
    
    # Travel time to the next location if we decide to meet them
    if i > 0:
        prev_friend = list(friends.keys())[i - 1]
        travel_time = travel_times[(current_location, friends[friend]["location"])]
        solver.add(Implies(And(meet_vars[prev_friend], meet_vars[friend]), meeting_start_times[friend] >= meeting_start_times[prev_friend] + friends[prev_friend]["duration"] + travel_time))
    
    # Update current location and time after meeting
    current_location = friends[friend]["location"]
    current_time = meeting_start_times[friend] + friends[friend]["duration"]

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for friend, details in friends.items():
        if model.evaluate(meet_vars[friend]):
            start_time = model[meeting_start_times[friend]].as_long()
            end_time = start_time + details["duration"]
            schedule.append((friend, start_time // 60, start_time % 60, end_time // 60, end_time % 60))
    schedule.sort(key=lambda x: x[1])  # Sort by start time
    print("SOLUTION:")
    for entry in schedule:
        print(f"{entry[0]}: {entry[1]:02}:{entry[2]:02} - {entry[3]:02}:{entry[4]:02}")
else:
    print("No solution found")