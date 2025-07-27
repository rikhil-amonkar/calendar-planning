from z3 import *
import json

# Initialize the solver
s = Optimize()

# Define the friends and their constraints
friends = [
    {"name": "Linda", "location": "Marina District", "start": 18*60, "end": 22*60, "duration": 30},
    {"name": "Kenneth", "location": "The Castro", "start": 14*60 + 45, "end": 16*60 + 15, "duration": 30},
    {"name": "Kimberly", "location": "Richmond District", "start": 14*60 + 15, "end": 22*60, "duration": 30},
    {"name": "Paul", "location": "Alamo Square", "start": 21*60, "end": 21*60 + 30, "duration": 15},
    {"name": "Carol", "location": "Financial District", "start": 10*60 + 15, "end": 12*60, "duration": 60},
    {"name": "Brian", "location": "Presidio", "start": 10*60, "end": 21*60 + 30, "duration": 75},
    {"name": "Laura", "location": "Mission District", "start": 16*60 + 15, "end": 20*60 + 30, "duration": 30},
    {"name": "Sandra", "location": "Nob Hill", "start": 9*60 + 15, "end": 18*60 + 30, "duration": 60},
    {"name": "Karen", "location": "Russian Hill", "start": 18*60 + 30, "end": 22*60, "duration": 75}
]

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5
    }
}

# Create variables for each friend's meeting start and end times
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "start": start,
        "end": end,
        "min_start": friend["start"],
        "max_end": friend["end"],
        "duration": friend["duration"]
    })
    # Constraint: meeting duration
    s.add(end == start + friend["duration"])
    # Constraint: within friend's availability
    s.add(start >= friend["start"])
    s.add(end <= friend["end"])

# Starting point is Pacific Heights at 9:00 AM (540 minutes)
current_time = 540
current_location = "Pacific Heights"

# For each pair of distinct meetings, add constraints that they are either non-overlapping or account for travel time.
for i in range(len(meetings)):
    for j in range(i + 1, len(meetings)):
        m1 = meetings[i]
        m2 = meetings[j]
        # Either m1 is before m2 with travel time, or vice versa
        s.add(Or(
            m1["end"] + travel_times[m1["location"]][m2["location"]] <= m2["start"],
            m2["end"] + travel_times[m2["location"]][m1["location"]] <= m1["start"]
        ))

# Also, the first meeting must start after the initial time plus travel time from Pacific Heights.
for m in meetings:
    s.add(m["start"] >= current_time + travel_times[current_location][m["location"]])

# Create a Boolean for each meeting being scheduled
met = [Bool(f"met_{m['name']}") for m in meetings]
for i, m in enumerate(meetings):
    s.add(Implies(met[i], And(m["start"] >= 0, m["end"] <= 24*60)))  # Ensure meeting is scheduled
    s.add(Implies(Not(met[i]), And(m["start"] == 0, m["end"] == 0)))  # If not met, set to dummy values

# Maximize the number of met friends
total_met = Sum([If(met[i], 1, 0) for i in range(len(meetings))])
s.maximize(total_met)

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    itinerary = []
    for m in meetings:
        start_val = model.evaluate(m["start"]).as_long()
        end_val = model.evaluate(m["end"]).as_long()
        if start_val > 0:  # Assuming start > 0 means the meeting is scheduled
            start_hour = start_val // 60
            start_minute = start_val % 60
            end_hour = end_val // 60
            end_minute = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": m["name"],
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:])))
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')