from z3 import *
import json

# Travel times between locations (minutes)
travel_times = {
    "Presidio": {
        "Pacific Heights": 11, "Golden Gate Park": 12, "Fisherman's Wharf": 19,
        "Marina District": 11, "Alamo Square": 19, "Sunset District": 15,
        "Nob Hill": 18, "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11, "Golden Gate Park": 15, "Fisherman's Wharf": 13,
        "Marina District": 6, "Alamo Square": 10, "Sunset District": 21,
        "Nob Hill": 8, "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11, "Pacific Heights": 16, "Fisherman's Wharf": 24,
        "Marina District": 16, "Alamo Square": 9, "Sunset District": 10,
        "Nob Hill": 20, "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17, "Pacific Heights": 12, "Golden Gate Park": 25,
        "Marina District": 9, "Alamo Square": 21, "Sunset District": 27,
        "Nob Hill": 11, "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10, "Pacific Heights": 7, "Golden Gate Park": 18,
        "Fisherman's Wharf": 10, "Alamo Square": 15, "Sunset District": 19,
        "Nob Hill": 12, "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17, "Pacific Heights": 10, "Golden Gate Park": 9,
        "Fisherman's Wharf": 19, "Marina District": 15, "Sunset District": 16,
        "Nob Hill": 11, "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16, "Pacific Heights": 21, "Golden Gate Park": 11,
        "Fisherman's Wharf": 29, "Marina District": 21, "Alamo Square": 17,
        "Nob Hill": 27, "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17, "Pacific Heights": 8, "Golden Gate Park": 17,
        "Fisherman's Wharf": 10, "Marina District": 11, "Alamo Square": 11,
        "Sunset District": 24, "North Beach": 8
    },
    "North Beach": {
        "Presidio": 17, "Pacific Heights": 8, "Golden Gate Park": 22,
        "Fisherman's Wharf": 5, "Marina District": 9, "Alamo Square": 16,
        "Sunset District": 27, "Nob Hill": 7
    }
}

# Friends' availability (excluding Kevin since he's unavailable)
friends = {
    "Michelle": {"location": "Golden Gate Park", "start": "20:00", "end": "21:00", "duration": 15},
    "Emily": {"location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "duration": 30},
    "Mark": {"location": "Marina District", "start": "18:15", "end": "19:45", "duration": 75},
    "Barbara": {"location": "Alamo Square", "start": "17:00", "end": "19:00", "duration": 120},
    "Laura": {"location": "Sunset District", "start": "19:00", "end": "21:15", "duration": 75},
    "Mary": {"location": "Nob Hill", "start": "17:30", "end": "19:00", "duration": 45},
    "Helen": {"location": "North Beach", "start": "11:00", "end": "12:15", "duration": 45}
}

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # Convert to minutes since 9:00 AM (540 minutes)

def minutes_to_time(minutes):
    total = 540 + minutes
    return f"{total//60:02d}:{total%60:02d}"

solver = Solver()

# Create variables for each meeting
meetings = {}
for name in friends:
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    meetings[name] = {"start": start, "end": end}

# Add meeting duration constraints
for name, data in friends.items():
    start_min = time_to_minutes(data["start"])
    end_min = time_to_minutes(data["end"])
    solver.add(meetings[name]["start"] >= start_min)
    solver.add(meetings[name]["end"] <= end_min)
    solver.add(meetings[name]["end"] == meetings[name]["start"] + data["duration"])

# Create variables to represent meeting order
n = len(friends)
order = [Int(f"order_{i}") for i in range(n)]
solver.add(Distinct(order))
for i in range(n):
    solver.add(order[i] >= 0, order[i] < n)

# Add sequencing constraints
friend_names = list(friends.keys())
for i in range(n):
    for j in range(i+1, n):
        # Get the two meetings being compared
        m1 = order[i]
        m2 = order[j]
        
        # Get the actual friend names based on order indices
        name1 = friend_names[m1]
        name2 = friend_names[m2]
        
        # Get locations and travel time
        loc1 = friends[name1]["location"]
        loc2 = friends[name2]["location"]
        travel = travel_times[loc1][loc2]
        
        # Add constraint that meeting1 must end before meeting2 starts minus travel time
        solver.add(If(m1 < m2, 
                     meetings[name1]["end"] + travel <= meetings[name2]["start"],
                     meetings[name2]["end"] + travel_times[loc2][loc1] <= meetings[name1]["start"]))

# Try to maximize number of meetings by minimizing start times
total_time = Int("total_time")
solver.add(total_time == sum([meetings[name]["start"] for name in friends]))
solver.minimize(total_time)

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model.evaluate(meetings[name]["start"]).as_long()
        end = model.evaluate(meetings[name]["end"]).as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    # Sort by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))