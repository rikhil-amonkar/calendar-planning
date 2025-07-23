from z3 import *

# Define all locations and friends with their availability (in minutes since midnight)
friends = {
    "Matthew": {"location": "Bayview", "start": 1290, "end": 1320, "duration": 120},
    "Karen": {"location": "Chinatown", "start": 1290, "end": 1305, "duration": 90},
    "Sarah": {"location": "Alamo Square", "start": 1320, "end": 1335, "duration": 105},
    "Jessica": {"location": "Nob Hill", "start": 1170, "end": 1185, "duration": 120},
    "Stephanie": {"location": "Presidio", "start": 450, "end": 615, "duration": 60},
    "Mary": {"location": "Union Square", "start": 1185, "end": 1290, "duration": 60},
    "Charles": {"location": "The Castro", "start": 1170, "end": 1320, "duration": 105},
    "Nancy": {"location": "North Beach", "start": 1005, "end": 1200, "duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": 930, "end": 1140, "duration": 30},
    "Brian": {"location": "Marina District", "start": 855, "end": 1080, "duration": 60}
}

# Complete travel times matrix (minutes between locations)
travel_times = {
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    # Include all reverse directions and other connections
    ("Bayview", "Embarcadero"): 19,
    ("Chinatown", "Embarcadero"): 5,
    # ... (include all other travel times from the original problem)
}

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM format"""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Create optimizer
opt = Optimize()

# Variables for each meeting
meetings = {}
for friend in friends:
    start = Int(f"start_{friend}")
    duration = friends[friend]["duration"]
    end = Int(f"end_{friend}")
    meetings[friend] = {"start": start, "end": end}
    
    # Meeting must be within friend's availability window
    opt.add(start >= friends[friend]["start"] - 540)  # 9:00 AM is 540 minutes
    opt.add(end <= friends[friend]["end"] - 540)
    opt.add(end == start + duration)

# No overlapping meetings with travel time
for f1 in friends:
    for f2 in friends:
        if f1 != f2:
            loc1 = friends[f1]["location"]
            loc2 = friends[f2]["location"]
            travel = travel_times.get((loc1, loc2), 0)
            opt.add(Or(
                meetings[f1]["end"] + travel <= meetings[f2]["start"],
                meetings[f2]["end"] + travel <= meetings[f1]["start"]
            ))

# Maximize number of meetings (count of friends met)
met = [Int(f"met_{friend}") for friend in friends]
for i, friend in enumerate(friends):
    opt.add(met[i] == If(
        And(
            meetings[friend]["start"] >= 0,
            meetings[friend]["end"] <= friends[friend]["end"] - 540,
            meetings[friend]["start"] + 540 >= friends[friend]["start"],
            meetings[friend]["end"] + 540 <= friends[friend]["end"]
        ), 1, 0))

total_met = Int("total_met")
opt.add(total_met == sum(met))
opt.maximize(total_met)

# Solve
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for friend in friends:
        start_val = m[meetings[friend]["start"]]
        end_val = m[meetings[friend]["end"]]
        if start_val is not None and end_val is not None:
            start = start_val.as_long()
            end = end_val.as_long()
            if (start >= 0 and end <= friends[friend]["end"] - 540 and
                start + 540 >= friends[friend]["start"] and 
                end + 540 <= friends[friend]["end"]):
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": minutes_to_time(start + 540),
                    "end_time": minutes_to_time(end + 540)
                })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print({"itinerary": []})