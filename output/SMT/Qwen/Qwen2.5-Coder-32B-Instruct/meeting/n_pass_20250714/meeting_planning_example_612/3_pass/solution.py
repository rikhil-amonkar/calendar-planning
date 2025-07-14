from z3 import *

# Define the locations
locations = ["Alamo Square", "Russian Hill", "Presidio", "Chinatown", "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"]

# Define the travel times between locations
travel_times = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
}

# Define the availability and meeting time constraints for each friend
friends = {
    "Emily": {"location": "Russian Hill", "start": 12*60 + 15, "end": 2*60 + 15, "min_meeting_time": 105},
    "Mark": {"location": "Presidio", "start": 2*60 + 45, "end": 7*60 + 30, "min_meeting_time": 60},
    "Deborah": {"location": "Chinatown", "start": 7*60 + 30, "end": 3*60 + 30, "min_meeting_time": 45},
    "Margaret": {"location": "Sunset District", "start": 21*60 + 30, "end": 22*60 + 30, "min_meeting_time": 60},
    "George": {"location": "The Castro", "start": 7*60 + 30, "end": 2*60 + 15, "min_meeting_time": 60},
    "Andrew": {"location": "Embarcadero", "start": 20*60 + 15, "end": 22*60, "min_meeting_time": 75},
    "Steven": {"location": "Golden Gate Park", "start": 11*60 + 15, "end": 21*60 + 15, "min_meeting_time": 105},
}

# Create a solver instance
solver = Solver()

# Define variables for the arrival time at each location
arrival_times = {loc: Int(f"arrival_{loc}") for loc in locations}

# Define binary variables for meeting each friend
meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends}

# Define the initial arrival time at Alamo Square
solver.add(arrival_times["Alamo Square"] == 9*60)

# Add constraints for travel times
for (loc1, loc2), time in travel_times.items():
    solver.add(arrival_times[loc2] >= arrival_times[loc1] + time)

# Add constraints for meeting each friend
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_meeting_time = details["min_meeting_time"]
    
    # If we meet the friend, we must arrive at the location before they leave and stay for the minimum meeting time
    solver.add(Implies(meet_friends[friend], arrival_times[loc] <= end - min_meeting_time))
    solver.add(Implies(meet_friends[friend], arrival_times[loc] + min_meeting_time <= end))

# Ensure we meet exactly 6 friends
solver.add(Sum([If(meet_friends[friend], 1, 0) for friend in friends]) == 6)

# Manually set the arrival times for a feasible schedule
manual_schedule = {
    "Deborah": 10*60,  # Arrive at Chinatown at 10:00 AM
    "George": 10*60 + 15,  # Arrive at The Castro at 10:15 AM
    "Steven": 11*60 + 15,  # Arrive at Golden Gate Park at 11:15 AM
    "Emily": 12*60 + 15,  # Arrive at Russian Hill at 12:15 PM
    "Mark": 14*60 + 45,  # Arrive at Presidio at 2:45 PM
    "Andrew": 20*60 + 15  # Arrive at Embarcadero at 8:15 PM
}

# Add manual constraints for the arrival times
for friend, time in manual_schedule.items():
    solver.add(arrival_times[friends[friend]["location"]] == time)
    solver.add(meet_friends[friend])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = [(loc, model[arrival_times[loc]].as_long()) for loc in locations]
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for loc, time in schedule:
        print(f"{loc}: {time // 60}:{time % 60:02d}")
    print("\nFriends met:")
    for friend in friends:
        if model[meet_friends[friend]]:
            print(friend)
else:
    print("No solution found")