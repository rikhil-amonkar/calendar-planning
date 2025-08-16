# Requires: z3-solver (pip install z3-solver)

from z3 import Int, Optimize, sat
from itertools import permutations, chain, combinations
import json

# Time helpers
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Data
start_location = "Fisherman's Wharf"
start_time = to_minutes("09:00")

# Directed travel times (in minutes)
travel = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
}

# Friends: name -> (location, window_start, window_end, min_duration)
friends = {
    "Emily":   ("Presidio",            to_minutes("16:15"), to_minutes("21:00"), 105),
    "Joseph":  ("Richmond District",   to_minutes("17:15"), to_minutes("22:00"), 120),
    "Melissa": ("Financial District",  to_minutes("15:45"), to_minutes("21:45"), 75),
}

people = list(friends.keys())

def all_subsets(iterable):
    s = list(iterable)
    for r in range(len(s), 0, -1):  # start from largest subsets
        for comb in combinations(s, r):
            yield comb

best = None  # (count, last_end_time, order_tuple, schedule_dict)

for subset in all_subsets(people):
    # Try all orders for this subset
    for order in permutations(subset):
        n = len(order)
        # Build an Optimize model
        opt = Optimize()
        s_vars = []
        e_vars = []

        # Create variables and constraints per meeting in order
        for i, person in enumerate(order):
            s = Int(f"s_{i}")
            e = Int(f"e_{i}")
            s_vars.append(s)
            e_vars.append(e)

            loc, w_start, w_end, dur = friends[person]

            # duration and window constraints
            opt.add(e == s + dur)
            opt.add(s >= w_start)
            opt.add(e <= w_end)

            # travel/sequence constraints
            if i == 0:
                # from start
                t = travel[(start_location, loc)]
                opt.add(s >= start_time + t)
            else:
                prev_person = order[i-1]
                prev_loc = friends[prev_person][0]
                t = travel[(prev_loc, loc)]
                opt.add(s >= e_vars[i-1] + t)

        # Objective: minimize the end time of the last meeting to reduce makespan
        if n > 0:
            h = opt.minimize(e_vars[-1])
        else:
            continue

        if opt.check() == sat:
            model = opt.model()
            schedule = []
            for i, person in enumerate(order):
                st = model[s_vars[i]].as_long()
                en = model[e_vars[i]].as_long()
                schedule.append((person, st, en))
            schedule_sorted = sorted(schedule, key=lambda x: x[1])  # already ordered
            last_end = schedule_sorted[-1][2]
            # Choose best by:
            # 1) maximize number of meetings
            # 2) minimize last_end
            # 3) tie-break by lexicographic order of names
            key = (len(order), -last_end * -1)  # placeholder; we'll compare explicitly below

            if best is None:
                best = (len(order), last_end, order, schedule_sorted)
            else:
                b_count, b_last_end, b_order, b_sched = best
                if len(order) > b_count:
                    best = (len(order), last_end, order, schedule_sorted)
                elif len(order) == b_count:
                    if last_end < b_last_end:
                        best = (len(order), last_end, order, schedule_sorted)
                    elif last_end == b_last_end:
                        # tie-break by lexicographic order tuple of names
                        if tuple(order) < tuple(b_order):
                            best = (len(order), last_end, order, schedule_sorted)

# Build the final itinerary JSON
itinerary = []
if best:
    _, _, _, sched = best
    for person, st, en in sched:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": fmt(st),
            "end_time": fmt(en),
        })

# Print the JSON dictionary
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))