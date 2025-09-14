from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times dictionary (in minutes)
travel = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19
    }
}

# List of friend meetings with constraints
# Times are expressed in minutes from midnight.
# For example 9:00 AM -> 540, 9:15 AM -> 555, 10:00 PM -> 1320, etc.
friends = [
    {"name": "David", "location": "Sunset District", "avail_start": 555, "avail_end": 1320, "min_duration": 15},
    {"name": "Kenneth", "location": "Union Square", "avail_start": 1275, "avail_end": 1305, "min_duration": 15},
    {"name": "Patricia", "location": "Nob Hill", "avail_start": 900, "avail_end": 1155, "min_duration": 120},
    {"name": "Mary", "location": "Marina District", "avail_start": 885, "avail_end": 1005, "min_duration": 45},
    {"name": "Charles", "location": "Richmond District", "avail_start": 1035, "avail_end": 1260, "min_duration": 15},
    {"name": "Joshua", "location": "Financial District", "avail_start": 870, "avail_end": 1035, "min_duration": 90},
    {"name": "Ronald", "location": "Embarcadero", "avail_start": 1095, "avail_end": 1245, "min_duration": 30},
    {"name": "George", "location": "The Castro", "avail_start": 855, "avail_end": 1140, "min_duration": 105},
    {"name": "Kimberly", "location": "Alamo Square", "avail_start": 540, "avail_end": 870, "min_duration": 105},
    {"name": "William", "location": "Presidio", "avail_start": 420, "avail_end": 765, "min_duration": 60}
]

# Arrival information: you start at Russian Hill at 9:00AM (540 minutes)
start_time_origin = 540
origin_location = "Russian Hill"

num_friends = len(friends)

opt = Optimize()

# Decision variables for each friend meeting
attend_vars = []
start_vars = []
end_vars = []
pos_vars = []

for i, f in enumerate(friends):
    attend = Bool(f"attend_{i}")
    start_var = Int(f"start_{i}")
    end_var = Int(f"end_{i}")
    pos = Int(f"pos_{i}")
    
    attend_vars.append(attend)
    start_vars.append(start_var)
    end_vars.append(end_var)
    pos_vars.append(pos)
    
    # If meeting is attended, start must be within the friend availability window (and allow the full meeting)
    # Also, if not attended, we fix the start time to 0 and pos to -1.
    opt.add(If(attend,
               And(start_var >= f["avail_start"],
                   start_var <= f["avail_end"] - f["min_duration"],
                   pos >= 0, pos < num_friends),
               And(start_var == 0, pos == -1)))
    # Define end time: if attended, end = start + duration; else, end = 0.
    opt.add(end_var == If(attend, start_var + f["min_duration"], 0))

    # For every attended meeting, ensure it doesn't start before the earliest possible arrival from origin.
    # For a meeting that is first in the schedule, we will enforce an extra constraint later using its order.
    # Here we add a weak lower bound: even if not first, one cannot start before what would be possible directly.
    earliest_from_origin = start_time_origin + travel[origin_location][f["location"]]
    opt.add(If(attend, start_var >= If(f["avail_start"] > earliest_from_origin, f["avail_start"], earliest_from_origin), True))

# Ordering constraints: use the pos variable to order attended meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        # If both meetings are attended, then their order (pos) must be different.
        opt.add(If(And(attend_vars[i], attend_vars[j]), pos_vars[i] != pos_vars[j], True))
        
        # If both are attended and i is scheduled before j then the finish time of i plus travel time must be <= start time of j.
        cond_ij = And(attend_vars[i], attend_vars[j], pos_vars[i] < pos_vars[j])
        opt.add(If(cond_ij,
                   start_vars[i] + friends[i]["min_duration"] + travel[friends[i]["location"]][friends[j]["location"]] <= start_vars[j],
                   True))
        # Similarly if j is scheduled before i.
        cond_ji = And(attend_vars[i], attend_vars[j], pos_vars[j] < pos_vars[i])
        opt.add(If(cond_ji,
                   start_vars[j] + friends[j]["min_duration"] + travel[friends[j]["location"]][friends[i]["location"]] <= start_vars[i],
                   True))

# For any meeting that is first in the order (pos == 0), ensure you can get there from the origin.
for i in range(num_friends):
    opt.add(If(And(attend_vars[i], pos_vars[i] == 0),
               start_time_origin + travel[origin_location][friends[i]["location"]] <= start_vars[i],
               True))

# Optional: Prevent meetings from overlapping in time even if travel constraints might not catch an edge case.
# (This disjunctive condition is already implicitly enforced by the ordering constraints above.)

# Objective: maximize the total number of meetings attended.
total_meetings = Sum([If(att, 1, 0) for att in attend_vars])
h = opt.maximize(total_meetings)

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    # Gather attended meetings with their order position
    attended = []
    for i in range(num_friends):
        if is_true(model.evaluate(attend_vars[i])):
            pos_val = model.evaluate(pos_vars[i]).as_long()
            s_val = model.evaluate(start_vars[i]).as_long()
            e_val = model.evaluate(end_vars[i]).as_long()
            attended.append({
                "index": i,
                "pos": pos_val,
                "name": friends[i]["name"],
                "location": friends[i]["location"],
                "start": s_val,
                "end": e_val
            })
    # Sort meetings by order position
    attended.sort(key=lambda x: x["pos"])
    
    itinerary = []
    for meeting in attended:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
        
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))