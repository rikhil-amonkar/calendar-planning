from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes between locations
travel_times = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,
    
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,
    
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Richmond District"): 18,
    
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,
    
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,
    
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,
    
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,
    
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Richmond District"): 25,
    
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
}

# Details for each friend meeting: location, available start/end (in minutes) and minimum meeting duration (in minutes)
friends = [
    {"name": "Emily", "location": "Pacific Heights", "avail_start": 555, "avail_end": 825, "duration": 120},
    {"name": "Helen", "location": "North Beach", "avail_start": 825, "avail_end": 1125, "duration": 30},
    {"name": "Kimberly", "location": "Golden Gate Park", "avail_start": 1125, "avail_end": 1275, "duration": 75},
    {"name": "James", "location": "Embarcadero", "avail_start": 630, "avail_end": 690, "duration": 30},
    {"name": "Linda", "location": "Haight-Ashbury", "avail_start": 450, "avail_end": 1155, "duration": 15},
    {"name": "Paul", "location": "Fisherman's Wharf", "avail_start": 885, "avail_end": 1125, "duration": 90},
    {"name": "Anthony", "location": "Mission District", "avail_start": 480, "avail_end": 885, "duration": 105},
    {"name": "Nancy", "location": "Alamo Square", "avail_start": 510, "avail_end": 825, "duration": 120},
    {"name": "William", "location": "Bayview", "avail_start": 1050, "avail_end": 1230, "duration": 120},
    {"name": "Margaret", "location": "Richmond District", "avail_start": 915, "avail_end": 1095, "duration": 45}
]

n = len(friends)
opt = Optimize()

# Decision variables:
# attends[i]: whether to schedule meeting with friend i.
# starts[i]: meeting start time (in minutes).
# ends[i]: meeting end time (in minutes).
# orders[i]: the position (order) in the itinerary (0 if not attended)
attends = [Bool(f"attend_{i}") for i in range(n)]
starts = [Int(f"start_{i}") for i in range(n)]
ends = [Int(f"end_{i}") for i in range(n)]
orders = [Int(f"order_{i}") for i in range(n)]

for i, friend in enumerate(friends):
    # If meeting is scheduled then meeting times must lie within the friend's available window
    # and the meeting must last at least the required duration. Also, assign a positive order.
    opt.add(If(attends[i],
               And(
                   starts[i] >= friend["avail_start"],
                   ends[i] <= friend["avail_end"],
                   ends[i] - starts[i] >= friend["duration"],
                   orders[i] >= 1, orders[i] <= n
               ),
               orders[i] == 0))
    # Ensure time values are non-negative.
    opt.add(starts[i] >= 0)
    opt.add(ends[i] >= 0)

# All scheduled meetings must have distinct order numbers.
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(attends[i], attends[j]), orders[i] != orders[j]))

# For consecutive meetings in the itinerary, add travel time constraints.
# If friend j follows friend i (i.e. order[j] == order[i] + 1), then j's meeting must start
# after i's meeting ends plus the travel time from i's location to j's location.
for i in range(n):
    for j in range(n):
        if i != j:
            opt.add(Implies(And(attends[i], attends[j], orders[j] == orders[i] + 1),
                            starts[j] >= ends[i] + travel_times[(friends[i]["location"], friends[j]["location"])]))

# The first meeting must be reachable from the starting location, Russian Hill at 9:00AM.
start_base = 540  # 9:00 AM in minutes
for i in range(n):
    opt.add(Implies(And(attends[i], orders[i] == 1),
                    starts[i] >= start_base + travel_times[("Russian Hill", friends[i]["location"])]))

# Objective: maximize the number of meetings attended.
opt.maximize(Sum([If(attends[i], 1, 0) for i in range(n)]))

if opt.check() == sat:
    model = opt.model()
    schedule = []
    # Gather meetings that were scheduled along with their order.
    for i in range(n):
        if is_true(model.evaluate(attends[i])):
            order_val = model.evaluate(orders[i]).as_long()
            schedule.append((order_val, i))
    schedule.sort(key=lambda x: x[0])
    
    itinerary = []
    for order_val, i in schedule:
        start_val = model.evaluate(starts[i]).as_long()
        end_val = model.evaluate(ends[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": friends[i]["location"],
            "person": friends[i]["name"],
            "start_time": minutes_to_time(start_val),
            "end_time": minutes_to_time(end_val)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))