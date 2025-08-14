from z3 import *

# Define the locations
locations = [
    "Nob Hill", "Embarcadero", "The Castro", "Haight-Ashbury",
    "Union Square", "North Beach", "Pacific Heights", "Chinatown",
    "Golden Gate Park", "Marina District", "Russian Hill"
]

# Define the travel times (in minutes)
travel_times = {
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
}

# Define the friends' availability and meeting duration requirements
friends = {
    "Mary": {"location": "Embarcadero", "start": 20*60, "end": 21*60+15, "min_duration": 75},
    "Kenneth": {"location": "The Castro", "start": 11*60+15, "end": 19*60+15, "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": 20*60, "end": 22*60, "min_duration": 120},
    "Sarah": {"location": "Union Square", "start": 11*60+45, "end": 14*60+30, "min_duration": 90},
    "Thomas": {"location": "North Beach", "start": 19*60+15, "end": 19*60+45, "min_duration": 15},
    "Daniel": {"location": "Pacific Heights", "start": 13*60+45, "end": 20*60+30, "min_duration": 15},
    "Richard": {"location": "Chinatown", "start": 8*60, "end": 18*60+45, "min_duration": 30},
    "Mark": {"location": "Golden Gate Park", "start": 17*60+30, "end": 21*60+30, "min_duration": 120},
    "David": {"location": "Marina District", "start": 20*60, "end": 21*60, "min_duration": 60},
    "Karen": {"location": "Russian Hill", "start": 13*60+15, "end": 18*60+30, "min_duration": 120},
}

# Create an optimizer instance
opt = Optimize()

# Define variables for the time spent at each location
time_at_location = {loc: Int(f"time_at_{loc}") for loc in locations}
start_time_at_location = {loc: Int(f"start_time_at_{loc}") for loc in locations}

# Initial location is Nob Hill at 9:00 AM
opt.add(start_time_at_location["Nob Hill"] == 9*60)

# Constraints for time spent at each location
for loc in locations:
    opt.add(time_at_location[loc] >= 0)

# Constraints for start times at each location
for i in range(1, len(locations)):
    prev_loc = locations[i-1]
    curr_loc = locations[i]
    opt.add(start_time_at_location[curr_loc] >= start_time_at_location[prev_loc] + travel_times[(prev_loc, curr_loc)])

# Constraints for friends' meetings
friend_meetings = []
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Binary variable to indicate if we meet the friend
    meet_friend = Bool(f"meet_{friend}")
    
    # Ensure we meet the friend only if we spend enough time there
    opt.add(meet_friend == And(time_at_location[loc] >= min_duration, 
                                start_time_at_location[loc] <= end - min_duration, 
                                start_time_at_location[loc] + time_at_location[loc] >= start))
    
    friend_meetings.append(meet_friend)

# Constraint to meet exactly 7 people
opt.add(Sum([If(meet_friend, 1, 0) for meet_friend in friend_meetings]) == 7)

# Maximize the total time spent meeting friends
total_meeting_time = Sum([If(meet_friend, time_at_location[friends[friend]["location"]], 0) for friend, meet_friend in zip(friends.keys(), friend_meetings)])
opt.maximize(total_meeting_time)

# Check if the constraints are satisfiable
if opt.check() == sat:
    model = opt.model()
    schedule = [(loc, model[start_time_at_location[loc]].as_long(), model[time_at_location[loc]].as_long()) for loc in locations]
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for loc, start, duration in schedule:
        print(f"{loc}: Start at {start//60}:{start%60:02d}, Duration {duration} minutes")
    print("Meetings:")
    for friend, meet_friend in zip(friends.keys(), friend_meetings):
        if model[meet_friend]:
            loc = friends[friend]["location"]
            start = model[start_time_at_location[loc]].as_long()
            duration = model[time_at_location[loc]].as_long()
            print(f"{friend} at {loc}: Start at {start//60}:{start%60:02d}, Duration {duration} minutes")
else:
    print("No solution found")