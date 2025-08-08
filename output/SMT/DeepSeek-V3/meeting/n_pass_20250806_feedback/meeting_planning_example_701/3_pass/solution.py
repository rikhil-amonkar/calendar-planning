from z3 import *
import json

# Define the travel times between locations
travel_times = {
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# Friends' availability and constraints
friends = {
    "Lisa": {"location": "The Castro", "start": (19, 15), "end": (21, 15), "min_duration": 120},
    "Daniel": {"location": "Nob Hill", "start": (8, 15), "end": (11, 0), "min_duration": 15},
    "Elizabeth": {"location": "Presidio", "start": (21, 15), "end": (22, 15), "min_duration": 45},
    "Steven": {"location": "Marina District", "start": (16, 30), "end": (20, 45), "min_duration": 90},
    "Timothy": {"location": "Pacific Heights", "start": (12, 0), "end": (18, 0), "min_duration": 90},
    "Ashley": {"location": "Golden Gate Park", "start": (20, 45), "end": (21, 45), "min_duration": 60},
    "Kevin": {"location": "Chinatown", "start": (12, 0), "end": (19, 0), "min_duration": 30},
    "Betty": {"location": "Richmond District", "start": (13, 15), "end": (15, 45), "min_duration": 30},
}

# Convert time to minutes since 9:00 AM (540 minutes)
def time_to_minutes(h, m):
    return h * 60 + m - 540  # 9:00 AM is 540 minutes

# Convert minutes back to time string
def minutes_to_time(m):
    total = m + 540
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for name in friends:
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    meetings[name] = {"start": start, "end": end, "location": friends[name]["location"]}
    # Add constraints for meeting duration and availability
    s.add(start >= time_to_minutes(*friends[name]["start"]))
    s.add(end <= time_to_minutes(*friends[name]["end"]))
    s.add(end - start >= friends[name]["min_duration"])

# Initial location: Mission District at 9:00 AM (0 minutes)
current_location = "Mission District"
current_time = 0

# Ensure meetings are scheduled in a feasible order with travel times
names = list(meetings.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        loc1 = meetings[names[i]]["location"]
        loc2 = meetings[names[j]]["location"]
        travel = travel_times.get((loc1, loc2), 0)
        s.add(Or(
            meetings[names[j]]["start"] >= meetings[names[i]]["end"] + travel,
            meetings[names[i]]["start"] >= meetings[names[j]]["end"] + travel
        ))

# Ensure all meetings are scheduled after the initial time
for name in meetings:
    s.add(meetings[name]["start"] >= 0)
    s.add(meetings[name]["end"] >= 0)

# Try to find a solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for name in meetings:
        start = m[meetings[name]["start"]].as_long()
        end = m[meetings[name]["end"]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')