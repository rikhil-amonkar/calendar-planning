from z3 import *
import json

# Define location indices
loc_index = {
    "Presidio": 0,
    "Richmond District": 1,
    "North Beach": 2,
    "Financial District": 3,
    "Golden Gate Park": 4,
    "Union Square": 5
}

# Travel time matrix (6x6)
travel = [
    [0, 7, 18, 23, 12, 22],   # from Presidio
    [7, 0, 17, 22, 9, 21],    # from Richmond District
    [17, 18, 0, 8, 22, 7],    # from North Beach
    [22, 21, 7, 0, 23, 9],    # from Financial District
    [11, 7, 24, 26, 0, 22],   # from Golden Gate Park
    [24, 20, 10, 9, 22, 0]    # from Union Square
]

# Friends data: (name, location index, available start (min), available end (min), min_duration (min))
friends = [
    ("Jason", loc_index["Richmond District"], 13*60, 20*60+45, 90),
    ("Melissa", loc_index["North Beach"], 18*60+45, 20*60+15, 45),
    ("Brian", loc_index["Financial District"], 9*60+45, 21*60+45, 15),
    ("Elizabeth", loc_index["Golden Gate Park"], 8*60+45, 21*60+30, 105),
    ("Laura", loc_index["Union Square"], 14*60+15, 19*60+30, 75)
]

n = len(friends)

# Create Z3 variables
meet_vars = [Bool(f"meet_{name}") for name, _, _, _, _ in friends]
start_vars = [Int(f"start_{name}") for name, _, _, _, _ in friends]

s = Solver()

# Constraints for each friend
for i in range(n):
    name, loc_idx, avail_start, avail_end, dur = friends[i]
    s.add(Implies(meet_vars[i], start_vars[i] >= avail_start))
    s.add(Implies(meet_vars[i], start_vars[i] >= 540 + travel[0][loc_idx]))  # 540 = 9:00 AM in minutes
    s.add(Implies(meet_vars[i], start_vars[i] + dur <= avail_end))

# Pairwise constraints for meetings
for i in range(n):
    for j in range(i+1, n):
        if i != j:
            _, loc_i, _, _, dur_i = friends[i]
            _, loc_j, _, _, dur_j = friends[j]
            # Condition: if both meetings happen, then either i is before j or j is before i
            cond1 = (start_vars[i] + dur_i + travel[loc_i][loc_j] <= start_vars[j])
            cond2 = (start_vars[j] + dur_j + travel[loc_j][loc_i] <= start_vars[i])
            s.add(Implies(And(meet_vars[i], meet_vars[j]), Or(cond1, cond2)))

# Optimize to maximize the number of friends met
opt = Optimize()
opt.add(s.assertions())
total_meet = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
opt.maximize(total_meet)

itinerary = []
if opt.check() == sat:
    model = opt.model()
    # Collect meetings that are scheduled
    for i in range(n):
        if model.evaluate(meet_vars[i]):
            name, _, _, _, dur = friends[i]
            start_val = model.evaluate(start_vars[i])
            start_min = start_val.as_long()
            end_min = start_min + dur
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))