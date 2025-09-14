#!/usr/bin/env python
from z3 import *
import json

def minutes_to_time(m):
    # Converts minutes (since midnight) to "H:MM" 24-hour format (no leading zero for hour)
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes) as a nested dictionary.
travel_times = {
    "Russian Hill": {
        "Pacific Heights": 7,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Mission District": 16,
        "Alamo Square": 15,
        "Bayview": 23,
        "Richmond District": 14
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "North Beach": 9,
        "Golden Gate Park": 15,
        "Embarcadero": 10,
        "Haight-Ashbury": 11,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
        "Alamo Square": 10,
        "Bayview": 22,
        "Richmond District": 12
    },
    "North Beach": {
        "Russian Hill": 4,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Alamo Square": 16,
        "Bayview": 25,
        "Richmond District": 18
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Pacific Heights": 16,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Mission District": 17,
        "Alamo Square": 9,
        "Bayview": 23,
        "Richmond District": 7
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Pacific Heights": 11,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Alamo Square": 19,
        "Bayview": 21,
        "Richmond District": 21
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Pacific Heights": 12,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
        "Alamo Square": 5,
        "Bayview": 18,
        "Richmond District": 10
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Pacific Heights": 12,
        "North Beach": 6,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Alamo Square": 21,
        "Bayview": 26,
        "Richmond District": 18
    },
    "Mission District": {
        "Russian Hill": 15,
        "Pacific Heights": 16,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Alamo Square": 11,
        "Bayview": 14,
        "Richmond District": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Bayview": 16,
        "Richmond District": 11
    },
    "Bayview": {
        "Russian Hill": 23,
        "Pacific Heights": 23,
        "North Beach": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 19,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Alamo Square": 16,
        "Richmond District": 25
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Alamo Square": 13,
        "Bayview": 27
    }
}

# Friends data with availability (times in minutes since midnight) and meeting requirements.
# Times: 9:00AM is 540, convert others accordingly.
friends = [
    {"name": "Emily", "location": "Pacific Heights", "avail_start": 555,  "avail_end": 825,  "min_duration": 120},  # 9:15 - 13:45
    {"name": "Helen", "location": "North Beach",     "avail_start": 825,  "avail_end": 1125, "min_duration": 30},   # 13:45 - 18:45
    {"name": "Kimberly", "location": "Golden Gate Park", "avail_start": 1125, "avail_end": 1275, "min_duration": 75}, # 18:45 - 21:15
    {"name": "James", "location": "Embarcadero",      "avail_start": 630,  "avail_end": 690,  "min_duration": 30},   # 10:30 - 11:30
    {"name": "Linda", "location": "Haight-Ashbury",   "avail_start": 450,  "avail_end": 1155, "min_duration": 15},   # 7:30 - 19:15
    {"name": "Paul", "location": "Fisherman's Wharf", "avail_start": 885,  "avail_end": 1125, "min_duration": 90},   # 14:45 - 18:45
    {"name": "Anthony", "location": "Mission District", "avail_start": 480, "avail_end": 885,  "min_duration": 105},  # 8:00 - 14:45
    {"name": "Nancy", "location": "Alamo Square",    "avail_start": 510,  "avail_end": 825,  "min_duration": 120},  # 8:30 - 13:45
    {"name": "William", "location": "Bayview",       "avail_start": 1050, "avail_end": 1230, "min_duration": 120},  # 17:30 - 20:30
    {"name": "Margaret", "location": "Richmond District", "avail_start": 915, "avail_end": 1095, "min_duration": 45}  # 15:15 - 18:15
]

# Starting point and time.
start_location = "Russian Hill"
start_time = 540  # 9:00 AM

# For non-attended meetings, we'll assign a high order value.
NON_ATTENDED_ORDER = 100

# Create an Optimize object.
opt = Optimize()

num_friends = len(friends)

# Create decision variables for each friend.
attended = [Bool(f"attended_{i}") for i in range(num_friends)]
starts = [Int(f"start_{i}") for i in range(num_friends)]
ends   = [Int(f"end_{i}") for i in range(num_friends)]
orders = [Int(f"order_{i}") for i in range(num_friends)]

# Add constraints for each friend.
for i, f in enumerate(friends):
    # If the meeting is attended, time constraints must hold.
    opt.add(Implies(attended[i], starts[i] >= f["avail_start"]))
    opt.add(Implies(attended[i], ends[i] <= f["avail_end"]))
    opt.add(Implies(attended[i], ends[i] - starts[i] >= f["min_duration"]))
    # Order constraints: if attended then order is in 0..(num_friends-1); if not, set to NON_ATTENDED_ORDER.
    opt.add(Implies(attended[i], And(orders[i] >= 0, orders[i] < num_friends)))
    opt.add(Implies(Not(attended[i]), orders[i] == NON_ATTENDED_ORDER))
    # For a meeting that is the first in the sequence (order 0), must also account for travel from starting location.
    opt.add(Implies(And(attended[i], orders[i] == 0),
                    starts[i] >= start_time + travel_times[start_location][f["location"]]))

# For every pair of meetings, add sequential ordering and travel constraints.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        # If both meetings are attended, they must have distinct orders.
        opt.add(Implies(And(attended[i], attended[j]), orders[i] != orders[j]))
        # If meeting i comes before meeting j then travel time from i to j must be respected.
        opt.add(Implies(And(attended[i], attended[j], orders[i] < orders[j]),
                        ends[i] + travel_times[friends[i]["location"]][friends[j]["location"]] <= starts[j]))
        # Similarly, if meeting j comes before meeting i.
        opt.add(Implies(And(attended[i], attended[j], orders[j] < orders[i]),
                        ends[j] + travel_times[friends[j]["location"]][friends[i]["location"]] <= starts[i]))

# Objective: maximize the number of meetings attended.
obj = Sum([If(attended[i], 1, 0) for i in range(num_friends)])
h = opt.maximize(obj)

if opt.check() == sat:
    model = opt.model()
    scheduled = []
    # Gather all attended meetings with their order, start and end times.
    for i in range(num_friends):
        if is_true(model.evaluate(attended[i])):
            order_val = model.evaluate(orders[i]).as_long()
            start_val = model.evaluate(starts[i]).as_long()
            end_val   = model.evaluate(ends[i]).as_long()
            scheduled.append({
                "person": friends[i]["name"],
                "location": friends[i]["location"],
                "start": start_val,
                "end": end_val,
                "order": order_val
            })
    # Sort meetings by their order in the itinerary.
    scheduled = sorted(scheduled, key=lambda x: x["order"])
    
    itinerary = []
    for item in scheduled:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time(item["start"]),
            "end_time": minutes_to_time(item["end"])
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))