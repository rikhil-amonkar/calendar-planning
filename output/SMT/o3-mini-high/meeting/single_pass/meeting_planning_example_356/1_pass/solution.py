from z3 import *
import json

# Convert clock times to minutes after midnight
def to_minutes(h, m):
    return h * 60 + m

# Friend meeting details:
#   avail_start and avail_end are in minutes after midnight,
#   min_duration is in minutes.
friends = {
    "Barbara": {
        "location": "North Beach",
        "avail_start": to_minutes(13, 45),   # 13:45 = 825
        "avail_end": to_minutes(20, 15),     # 20:15 = 1215
        "min_duration": 60
    },
    "Margaret": {
        "location": "Presidio",
        "avail_start": to_minutes(10, 15),   # 10:15 = 615
        "avail_end": to_minutes(15, 15),     # 15:15 = 915
        "min_duration": 30
    },
    "Kevin": {
        "location": "Haight-Ashbury",
        "avail_start": to_minutes(20, 0),    # 20:00 = 1200
        "avail_end": to_minutes(20, 45),     # 20:45 = 1245
        "min_duration": 30
    },
    "Kimberly": {
        "location": "Union Square",
        "avail_start": to_minutes(7, 45),    # 07:45 = 465 (but note travel constraints apply)
        "avail_end": to_minutes(16, 45),     # 16:45 = 1005
        "min_duration": 30
    }
}

# Starting point: You arrive at Bayview at 9:00AM.
origin = "Bayview"
arrival_time = to_minutes(9, 0)  # 9:00 = 540

# Travel times (in minutes) between locations
travel_times = {
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 17,
    
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,
    
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 17,
    
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18
}

# Create Z3 integer variables for the meeting start and end times (in minutes)
meeting_starts = {}
meeting_ends = {}

for friend in friends:
    meeting_starts[friend] = Int(f"start_{friend}")
    meeting_ends[friend] = Int(f"end_{friend}")

solver = Solver()

# Add constraints for each friend meeting:
for friend, info in friends.items():
    loc = info["location"]
    # Constraint from Bayview: you must travel from Bayview to the meeting location.
    travel_from_origin = travel_times[(origin, loc)]
    solver.add(meeting_starts[friend] >= arrival_time + travel_from_origin)
    
    # The meeting cannot start before the friend is available.
    solver.add(meeting_starts[friend] >= info["avail_start"])
    
    # The meeting must finish within the friend’s available window.
    solver.add(meeting_ends[friend] <= info["avail_end"])
    
    # The meeting must last at least the required duration.
    solver.add(meeting_ends[friend] - meeting_starts[friend] >= info["min_duration"])

# For every pair of meetings, add non-overlap constraints with travel-time in mind.
friend_list = list(friends.keys())
for i in range(len(friend_list)):
    for j in range(i + 1, len(friend_list)):
        f1 = friend_list[i]
        f2 = friend_list[j]
        loc1 = friends[f1]["location"]
        loc2 = friends[f2]["location"]
        # Travel times between the two meeting locations.
        travel_1_to_2 = travel_times[(loc1, loc2)]
        travel_2_to_1 = travel_times[(loc2, loc1)]
        # Either f1 happens before f2 (including travel time)
        # or f2 happens before f1.
        constraint_f1_before_f2 = meeting_ends[f1] + travel_1_to_2 <= meeting_starts[f2]
        constraint_f2_before_f1 = meeting_ends[f2] + travel_2_to_1 <= meeting_starts[f1]
        solver.add(Or(constraint_f1_before_f2, constraint_f2_before_f1))

# Solve the scheduling constraints.
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for friend in friends:
        start_val = model[meeting_starts[friend]].as_long()
        end_val = model[meeting_ends[friend]].as_long()
        schedule.append((start_val, friend, end_val))
    
    # Sort the meetings by their start time.
    schedule.sort(key=lambda x: x[0])
    
    # Utility to convert minutes to HH:MM (24-hour format)
    def format_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = []
    for start_val, friend, end_val in schedule:
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": format_time(start_val),
            "end_time": format_time(end_val)
        })
    
    result = {"itinerary": itinerary}
    # Print the result as a JSON-formatted dictionary.
    print(json.dumps(result, indent=4))
else:
    print("No solution found")