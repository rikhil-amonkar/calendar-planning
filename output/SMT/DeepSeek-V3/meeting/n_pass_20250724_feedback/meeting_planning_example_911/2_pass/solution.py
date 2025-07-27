from z3 import *
import json

# Define the friends and their availability
friends = {
    "Steven": {"location": "North Beach", "start": "17:30", "end": "20:30", "duration": 15},
    "Sarah": {"location": "Golden Gate Park", "start": "17:00", "end": "19:15", "duration": 75},
    "Brian": {"location": "Embarcadero", "start": "14:15", "end": "16:00", "duration": 105},
    "Stephanie": {"location": "Haight-Ashbury", "start": "10:15", "end": "12:15", "duration": 75},
    "Melissa": {"location": "Richmond District", "start": "14:00", "end": "19:30", "duration": 30},
    "Nancy": {"location": "Nob Hill", "start": "08:15", "end": "12:45", "duration": 90},
    "David": {"location": "Marina District", "start": "11:15", "end": "13:15", "duration": 120},
    "James": {"location": "Presidio", "start": "15:00", "end": "18:15", "duration": 120},
    "Elizabeth": {"location": "Union Square", "start": "11:30", "end": "21:00", "duration": 60},
    "Robert": {"location": "Financial District", "start": "13:15", "end": "15:15", "duration": 45}
}

# Travel times (in minutes) between locations
travel_times = {
    "The Castro": {
        "North Beach": 20, "Golden Gate Park": 11, "Embarcadero": 22, "Haight-Ashbury": 6,
        "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Presidio": 20,
        "Union Square": 19, "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23, "Golden Gate Park": 22, "Embarcadero": 6, "Haight-Ashbury": 18,
        "Richmond District": 18, "Nob Hill": 7, "Marina District": 9, "Presidio": 17,
        "Union Square": 7, "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13, "North Beach": 23, "Embarcadero": 25, "Haight-Ashbury": 7,
        "Richmond District": 7, "Nob Hill": 20, "Marina District": 16, "Presidio": 11,
        "Union Square": 22, "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25, "North Beach": 5, "Golden Gate Park": 25, "Haight-Ashbury": 21,
        "Richmond District": 21, "Nob Hill": 10, "Marina District": 12, "Presidio": 20,
        "Union Square": 10, "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6, "North Beach": 19, "Golden Gate Park": 7, "Embarcadero": 20,
        "Richmond District": 10, "Nob Hill": 15, "Marina District": 17, "Presidio": 15,
        "Union Square": 19, "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16, "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
        "Haight-Ashbury": 10, "Nob Hill": 17, "Marina District": 9, "Presidio": 7,
        "Union Square": 21, "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17, "North Beach": 8, "Golden Gate Park": 17, "Embarcadero": 9,
        "Haight-Ashbury": 13, "Richmond District": 14, "Marina District": 11, "Presidio": 17,
        "Union Square": 7, "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22, "North Beach": 11, "Golden Gate Park": 18, "Embarcadero": 14,
        "Haight-Ashbury": 16, "Richmond District": 11, "Nob Hill": 12, "Presidio": 10,
        "Union Square": 16, "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21, "North Beach": 18, "Golden Gate Park": 12, "Embarcadero": 20,
        "Haight-Ashbury": 15, "Richmond District": 7, "Nob Hill": 18, "Marina District": 11,
        "Union Square": 22, "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Golden Gate Park": 22, "Embarcadero": 11,
        "Haight-Ashbury": 18, "Richmond District": 20, "Nob Hill": 9, "Marina District": 18,
        "Presidio": 24, "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20, "North Beach": 7, "Golden Gate Park": 23, "Embarcadero": 4,
        "Haight-Ashbury": 19, "Richmond District": 21, "Nob Hill": 8, "Marina District": 15,
        "Presidio": 22, "Union Square": 9
    }
}

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for name in friends:
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    meetings[name] = {"start": start, "end": end}

# Initial constraints: start at The Castro at 9:00 AM (540 minutes)
current_location = "The Castro"
current_time = 540  # 9:00 AM in minutes

# Add constraints for each friend's availability and duration
for name, info in friends.items():
    start_min = time_to_minutes(info["start"])
    end_min = time_to_minutes(info["end"])
    duration = info["duration"]
    
    s.add(meetings[name]["start"] >= start_min)
    s.add(meetings[name]["end"] <= end_min)
    s.add(meetings[name]["end"] == meetings[name]["start"] + duration)

# Define a variable for the order of meetings (permutation)
order = [Int(f"order_{i}") for i in range(len(friends))]
s.add(Distinct(order))
for i in range(len(friends)):
    s.add(And(order[i] >= 0, order[i] < len(friends)))

# Add travel time constraints between consecutive meetings
for i in range(len(friends) - 1):
    current_idx = order[i]
    next_idx = order[i + 1]
    
    # Get the names of the current and next friends
    current_name = None
    next_name = None
    for name in friends:
        if current_idx == list(friends.keys()).index(name):
            current_name = name
        if next_idx == list(friends.keys()).index(name):
            next_name = name
    
    if current_name and next_name:
        current_loc = friends[current_name]["location"]
        next_loc = friends[next_name]["location"]
        travel_time = travel_times[current_loc][next_loc]
        
        s.add(meetings[next_name]["start"] >= meetings[current_name]["end"] + travel_time)

# Ensure all meetings are scheduled after the start time
for name in friends:
    s.add(meetings[name]["start"] >= current_time)

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    # Get the order of meetings
    order_indices = [m[o].as_long() for o in order]
    friend_names = list(friends.keys())
    ordered_meetings = [friend_names[i] for i in order_indices]
    
    itinerary = []
    for name in ordered_meetings:
        start = m[meetings[name]["start"]].as_long()
        end = m[meetings[name]["end"]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")