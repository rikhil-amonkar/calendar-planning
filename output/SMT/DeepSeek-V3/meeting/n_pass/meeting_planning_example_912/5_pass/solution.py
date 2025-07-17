from z3 import *
import json

# Define locations and travel times with consistent naming
locations = [
    "Union Square", "Presidio", "Alamo Square", "Marina District", "Financial District",
    "Nob Hill", "Sunset District", "Chinatown", "Russian Hill", "North Beach", "Haight-Ashbury"
]

# Complete travel times matrix with all locations
travel_times = {
    "Union Square": {
        "Presidio": 24, "Alamo Square": 15, "Marina District": 18, "Financial District": 9,
        "Nob Hill": 9, "Sunset District": 27, "Chinatown": 7, "Russian Hill": 13,
        "North Beach": 10, "Haight-Ashbury": 18
    },
    "Presidio": {
        "Union Square": 22, "Alamo Square": 19, "Marina District": 11, "Financial District": 23,
        "Nob Hill": 18, "Sunset District": 15, "Chinatown": 21, "Russian Hill": 14,
        "North Beach": 18, "Haight-Ashbury": 15
    },
    "Alamo Square": {
        "Union Square": 14, "Presidio": 17, "Marina District": 15, "Financial District": 17,
        "Nob Hill": 11, "Sunset District": 16, "Chinatown": 15, "Russian Hill": 13,
        "North Beach": 15, "Haight-Ashbury": 5
    },
    "Marina District": {
        "Union Square": 16, "Presidio": 10, "Alamo Square": 15, "Financial District": 17,
        "Nob Hill": 12, "Sunset District": 19, "Chinatown": 15, "Russian Hill": 8,
        "North Beach": 11, "Haight-Ashbury": 16
    },
    "Financial District": {
        "Union Square": 9, "Presidio": 22, "Alamo Square": 17, "Marina District": 15,
        "Nob Hill": 8, "Sunset District": 30, "Chinatown": 5, "Russian Hill": 11,
        "North Beach": 7, "Haight-Ashbury": 19
    },
    "Nob Hill": {
        "Union Square": 7, "Presidio": 17, "Alamo Square": 11, "Marina District": 11,
        "Financial District": 9, "Sunset District": 24, "Chinatown": 6, "Russian Hill": 5,
        "North Beach": 8, "Haight-Ashbury": 13
    },
    "Sunset District": {
        "Union Square": 30, "Presidio": 16, "Alamo Square": 17, "Marina District": 21,
        "Financial District": 30, "Nob Hill": 27, "Chinatown": 30, "Russian Hill": 24,
        "North Beach": 28, "Haight-Ashbury": 15
    },
    "Chinatown": {
        "Union Square": 7, "Presidio": 19, "Alamo Square": 17, "Marina District": 12,
        "Financial District": 5, "Nob Hill": 9, "Sunset District": 29, "Russian Hill": 7,
        "North Beach": 3, "Haight-Ashbury": 19
    },
    "Russian Hill": {
        "Union Square": 10, "Presidio": 14, "Alamo Square": 15, "Marina District": 7,
        "Financial District": 11, "Nob Hill": 5, "Sunset District": 23, "Chinatown": 9,
        "North Beach": 5, "Haight-Ashbury": 17
    },
    "North Beach": {
        "Union Square": 7, "Presidio": 17, "Alamo Square": 16, "Marina District": 9,
        "Financial District": 8, "Nob Hill": 7, "Sunset District": 27, "Chinatown": 6,
        "Russian Hill": 4, "Haight-Ashbury": 18
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Presidio": 15, "Alamo Square": 5, "Marina District": 17,
        "Financial District": 21, "Nob Hill": 15, "Sunset District": 15, "Chinatown": 19,
        "Russian Hill": 17, "North Beach": 19
    }
}

friends = [
    {"name": "Kimberly", "location": "Presidio", "start": "15:30", "end": "16:00", "min_duration": 15, "required": False},
    {"name": "Elizabeth", "location": "Alamo Square", "start": "19:15", "end": "20:15", "min_duration": 15, "required": False},
    {"name": "Joshua", "location": "Marina District", "start": "10:30", "end": "14:15", "min_duration": 45, "required": True},
    {"name": "Sandra", "location": "Financial District", "start": "19:30", "end": "20:15", "min_duration": 45, "required": False},
    {"name": "Kenneth", "location": "Nob Hill", "start": "12:45", "end": "21:45", "min_duration": 30, "required": True},
    {"name": "Betty", "location": "Sunset District", "start": "14:00", "end": "19:00", "min_duration": 60, "required": True},
    {"name": "Deborah", "location": "Chinatown", "start": "17:15", "end": "20:30", "min_duration": 15, "required": False},
    {"name": "Barbara", "location": "Russian Hill", "start": "17:30", "end": "21:15", "min_duration": 120, "required": False},
    {"name": "Steven", "location": "North Beach", "start": "17:45", "end": "20:45", "min_duration": 90, "required": False},
    {"name": "Daniel", "location": "Haight-Ashbury", "start": "18:30", "end": "18:45", "min_duration": 15, "required": False}
]

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # 9:00 AM = 540 minutes

def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Initialize solver
opt = Optimize()

# Create variables
meetings = []
for friend in friends:
    scheduled = Bool(f"scheduled_{friend['name']}")
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    duration = Int(f"duration_{friend['name']}")
    
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "scheduled": scheduled,
        "start": start,
        "end": end,
        "duration": duration,
        "min_duration": friend["min_duration"],
        "window_start": time_to_minutes(friend["start"]),
        "window_end": time_to_minutes(friend["end"]),
        "required": friend["required"]
    })

# Add constraints
for m in meetings:
    # Required meetings must be scheduled
    if m["required"]:
        opt.add(m["scheduled"])
    
    # If scheduled, enforce time constraints
    opt.add(Implies(m["scheduled"],
              And(m["start"] >= m["window_start"],
                  m["end"] <= m["window_end"],
                  m["duration"] >= m["min_duration"],
                  m["end"] == m["start"] + m["duration"])))

# No overlapping for scheduled meetings
for i in range(len(meetings)):
    for j in range(i+1, len(meetings)):
        m1 = meetings[i]
        m2 = meetings[j]
        opt.add(Implies(And(m1["scheduled"], m2["scheduled"]),
                  Or(m1["end"] + travel_times[m1["location"]][m2["location"]] <= m2["start"],
                     m2["end"] + travel_times[m2["location"]][m1["location"]] <= m1["start"])))

# Maximize number of scheduled meetings
total_scheduled = Int("total_scheduled")
opt.add(total_scheduled == Sum([If(m["scheduled"], 1, 0) for m in meetings]))
opt.maximize(total_scheduled)

# Solve
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for m in meetings:
        if model.evaluate(m["scheduled"]):
            start = model.evaluate(m["start"]).as_long()
            end = model.evaluate(m["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": m["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')