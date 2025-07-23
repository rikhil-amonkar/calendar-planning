from z3 import *

# Define all locations and friends with their availability
locations = ["Embarcadero", "Bayview", "Chinatown", "Alamo Square", "Nob Hill", 
             "Presidio", "Union Square", "The Castro", "North Beach", 
             "Fisherman's Wharf", "Marina District"]

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
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10
}

def minutes_to_time(minutes):
    total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
    h = total_minutes // 60
    m = total_minutes % 60
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
    
    # Meeting must be within friend's availability
    opt.add(start >= friends[friend]["start"] - 540)
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
    opt.add(met[i] == If(And(meetings[friend]["start"] >= 0, 
                             meetings[friend]["end"] <= friends[friend]["end"] - 540), 
                         1, 0))

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
            if start >= 0 and end <= friends[friend]["end"] - 540:
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: int(x["start_time"].replace(":", "")))
    print({"itinerary": itinerary})
else:
    print({"itinerary": []})