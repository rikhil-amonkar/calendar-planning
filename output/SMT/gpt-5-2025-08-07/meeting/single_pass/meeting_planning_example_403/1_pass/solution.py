# Solve the scheduling problem using Z3 and output the optimal itinerary as JSON.
# Objective: maximize the number of friends met while respecting travel times and availability windows.
from z3 import Int, Optimize, And, Or, If, Sum
from itertools import permutations
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def from_minutes(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Locations
US = "Union Square"
GGP = "Golden Gate Park"
PH = "Pacific Heights"
PR = "Presidio"
CT = "Chinatown"
CA = "The Castro"

# Travel times in minutes (directed as given)
travel = {
    US: {GGP: 22, PH: 15, PR: 24, CT: 7,  CA: 19},
    GGP:{US: 22, PH: 16, PR: 11, CT: 23, CA: 13},
    PH: {US: 12, GGP: 15, PR: 11, CT: 11, CA: 16},
    PR: {US: 22, GGP: 12, PH: 11, CT: 21, CA: 21},
    CT: {US: 7,  GGP: 23, PH: 10, PR: 19, CA: 20},
    CA: {US: 19, GGP: 11, PH: 16, PR: 20, CT: 20},
}

def t(a, b):
    # Return travel time from a to b (int minutes)
    return travel[a][b]

start_location = US
start_time = to_minutes("09:00")

# Friends data
friends = {
    "Andrew":  {"location": GGP, "window": (to_minutes("11:45"), to_minutes("14:30")), "min_dur": 75},
    "Sarah":   {"location": PH,  "window": (to_minutes("16:15"), to_minutes("18:45")), "min_dur": 15},
    "Nancy":   {"location": PR,  "window": (to_minutes("17:30"), to_minutes("19:15")), "min_dur": 60},
    "Rebecca": {"location": CT,  "window": (to_minutes("09:45"), to_minutes("21:30")), "min_dur": 90},
    "Robert":  {"location": CA,  "window": (to_minutes("08:30"), to_minutes("14:15")), "min_dur": 30},
}

people = ["Robert", "Rebecca", "Andrew", "Sarah", "Nancy"]

# Try to meet as many as possible: search k from 5 down to 1
best_solution = None  # (k, end_last, sum_starts, sum_ends, perm, schedule_dict)
for k in range(len(people), 0, -1):
    best_for_k = None
    # Enumerate all permutations of people
    for perm in permutations(people, len(people)):
        opt = Optimize()
        s_vars = []
        e_vars = []
        # Create variables for the first k people in this order
        for i in range(k):
            s = Int(f"s_{i}")
            e = Int(f"e_{i}")
            s_vars.append(s)
            e_vars.append(e)

            p = perm[i]
            loc = friends[p]["location"]
            w_start, w_end = friends[p]["window"]
            min_dur = friends[p]["min_dur"]

            opt.add(s >= w_start, e <= w_end, e - s >= min_dur)

        # Travel/time ordering constraints
        if k >= 1:
            first_loc = friends[perm[0]]["location"]
            opt.add(s_vars[0] >= start_time + t(start_location, first_loc))
        for i in range(1, k):
            prev_loc = friends[perm[i-1]]["location"]
            curr_loc = friends[perm[i]]["location"]
            opt.add(s_vars[i] >= e_vars[i-1] + t(prev_loc, curr_loc))

        # Objectives: minimize end of last, then sum of ends, then sum of starts (to pick earlier feasible plan)
        end_last = e_vars[-1]
        opt.minimize(end_last)
        opt.minimize(Sum(e_vars))
        opt.minimize(Sum(s_vars))

        if opt.check() == 1:  # sat
            m = opt.model()
            schedule = []
            for i in range(k):
                p = perm[i]
                s = m[s_vars[i]].as_long()
                e = m[e_vars[i]].as_long()
                schedule.append((p, s, e))
            end_last_val = m[end_last].as_long()
            sum_starts = sum(m[s_vars[i]].as_long() for i in range(k))
            sum_ends = sum(m[e_vars[i]].as_long() for i in range(k))

            key = (end_last_val, sum_ends, sum_starts)
            if best_for_k is None or key < best_for_k[0]:
                best_for_k = (key, perm, schedule)

    if best_for_k is not None:
        best_solution = (k, best_for_k[1], best_for_k[2])
        break

# Build JSON itinerary
itinerary = []
if best_solution:
    k, perm, schedule = best_solution
    for (person, s, e) in schedule:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": from_minutes(s),
            "end_time": from_minutes(e),
        })

# Print JSON dictionary
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))