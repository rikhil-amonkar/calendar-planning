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

# Travel times between locations
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
    # ... (other locations remain the same)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

s = Optimize()

# Create variables for each meeting
meetings = {}
for name in friends:
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    meetings[name] = {"start": start, "end": end}

# Initial constraints
current_time = 540  # 9:00 AM
current_location = "The Castro"

# Meeting constraints
for name, info in friends.items():
    start_min = time_to_minutes(info["start"])
    end_min = time_to_minutes(info["end"])
    duration = info["duration"]
    
    s.add(meetings[name]["start"] >= start_min)
    s.add(meetings[name]["end"] <= end_min)
    s.add(meetings[name]["end"] == meetings[name]["start"] + duration)

# Create a list of all possible meeting orders
all_meetings = list(friends.keys())
num_meetings = len(all_meetings)

# Variables to track meeting order
position = [Int(f"pos_{i}") for i in range(num_meetings)]
s.add(Distinct(position))
for p in position:
    s.add(p >= 0, p < num_meetings)

# Variables to track locations
locations = [String(f"loc_{i}") for i in range(num_meetings + 1)]
s.add(locations[0] == current_location)

# Variables to track times
times = [Int(f"time_{i}") for i in range(num_meetings + 1)]
s.add(times[0] == current_time)

# Meeting order constraints
for i in range(num_meetings):
    # Use Element to properly handle Z3 array indexing
    meeting_idx = position[i]
    meeting_name = String(f"meeting_name_{i}")
    
    # Create a mapping from index to meeting name
    for idx in range(num_meetings):
        s.add(If(meeting_idx == idx, meeting_name == all_meetings[idx], True))
    
    # Location constraint
    s.add(locations[i+1] == friends[meeting_name]["location"])
    
    # Time constraint
    travel_time = Int(f"travel_{i}")
    s.add(travel_time == travel_times[locations[i]][locations[i+1]])
    s.add(meetings[meeting_name]["start"] >= times[i] + travel_time)
    s.add(times[i+1] == meetings[meeting_name]["end"])

# Maximize number of meetings
s.maximize(Sum([If(meetings[name]["start"] >= 0, 1, 0) for name in friends]))

if s.check() == sat:
    m = s.model()
    # Get ordered meetings
    meeting_order = []
    for i in range(num_meetings):
        pos = m.evaluate(position[i]).as_long()
        meeting_order.append((pos, all_meetings[pos]))
    
    ordered_meetings = [name for (pos, name) in sorted(meeting_order)]
    
    itinerary = []
    for name in ordered_meetings:
        start = m.evaluate(meetings[name]["start"]).as_long()
        end = m.evaluate(meetings[name]["end"]).as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")