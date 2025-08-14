from z3 import *

# Define the locations
locations = [
    "Chinatown", "Embarcadero", "Pacific Heights", "Russian Hill",
    "Haight-Ashbury", "Golden Gate Park", "Fisherman's Wharf",
    "Sunset District", "The Castro"
]

# Define the travel times between locations
travel_times = {
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "The Castro"): 17,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Sunset District"): 17,
}

# Define the friends' availability and meeting requirements
friends = {
    "Richard": {"location": "Embarcadero", "start": 15*60+15, "end": 18*60+45, "min_meeting": 90},
    "Mark": {"location": "Pacific Heights", "start": 15*60, "end": 17*60, "min_meeting": 45},
    "Matthew": {"location": "Russian Hill", "start": 17*60+30, "end": 21*60, "min_meeting": 90},
    "Rebecca": {"location": "Haight-Ashbury", "start": 14*60+45, "end": 18*60, "min_meeting": 60},
    "Melissa": {"location": "Golden Gate Park", "start": 13*60+45, "end": 17*60+30, "min_meeting": 90},
    "Margaret": {"location": "Fisherman's Wharf", "start": 14*60+45, "end": 20*60+15, "min_meeting": 15},
    "Emily": {"location": "Sunset District", "start": 15*60+45, "end": 17*60, "min_meeting": 45},
    "George": {"location": "The Castro", "start": 14*60, "end": 16*15, "min_meeting": 75},
}

# Create a solver instance
solver = Solver()

# Define variables for the time spent at each location
visit_times = {loc: Int(f"visit_{loc}") for loc in locations}

# Define binary variables for meeting each friend
meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends}

# Add constraints for the initial visit time
solver.add(visit_times["Chinatown"] == 9*60)

# Add constraints for the travel times and visit times
for i in range(len(locations)):
    for j in range(i + 1, len(locations)):
        loc1, loc2 = locations[i], locations[j]
        travel_time = travel_times[(loc1, loc2)]
        solver.add(Or(visit_times[loc2] >= visit_times[loc1] + travel_time, *[(Not(meet_friends[friend])) for friend in friends if friends[friend]["location"] == loc2]))
        solver.add(Or(visit_times[loc1] >= visit_times[loc2] + travel_time, *[(Not(meet_friends[friend])) for friend in friends if friends[friend]["location"] == loc1]))

# Add constraints for meeting friends
for friend, details in friends.items():
    loc, start, end, min_meeting = details["location"], details["start"], details["end"], details["min_meeting"]
    solver.add(Implies(meet_friends[friend], visit_times[loc] + min_meeting <= end))
    solver.add(Implies(meet_friends[friend], visit_times[loc] >= start))

# Add constraint to meet exactly 5 friends
solver.add(Sum([If(meet_friends[friend], 1, 0) for friend in friends]) == 5)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = {loc: model[visit_times[loc]].as_long() for loc in locations}
    meetings = {friend: model[meet_friends[friend]] for friend in friends}
    print("SOLUTION:")
    for loc in locations:
        print(f"{loc}: {schedule[loc]//60}:{schedule[loc]%60:02}")
    print("\nMeetings:")
    for friend, meet in meetings.items():
        print(f"{friend}: {'Yes' if meet else 'No'}")
else:
    print("No solution found")