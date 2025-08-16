# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Bool, If, And, Or, sat
import json

# Time helpers
def hm_to_minutes(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def minutes_to_hm(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Problem data
base_start = hm_to_minutes("09:00")

# Directed travel times (minutes)
travel = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Chinatown"): 16,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Union Square"): 7,
}

friends = {
    "Emily":   {"location": "Alamo Square", "window": ("11:45", "15:15"), "min_minutes": 105},
    "Barbara": {"location": "Union Square", "window": ("16:45", "18:15"), "min_minutes": 60},
    "William": {"location": "Chinatown",    "window": ("17:15", "19:00"), "min_minutes": 105},
}

# Convert windows to absolute minutes
for p, info in friends.items():
    ws, we = info["window"]
    info["wstart"] = hm_to_minutes(ws)
    info["wend"] = hm_to_minutes(we)

# Build Z3 model
opt = Optimize()
opt.set(priority='lex')  # lexicographic: maximize count first, then total duration

meet = {p: Bool(f"meet_{p}") for p in friends}
start = {p: Int(f"start_{p}") for p in friends}
end   = {p: Int(f"end_{p}") for p in friends}

# Reasonable horizon: end of last window
max_end = max(info["wend"] for info in friends.values())

for p, info in friends.items():
    # Domain bounds
    opt.add(start[p] >= base_start, start[p] <= max_end)
    opt.add(end[p]   >= base_start, end[p]   <= max_end)

    # If meet, enforce window and minimum duration
    opt.add(If(meet[p], start[p] >= info["wstart"], True))
    opt.add(If(meet[p], end[p]   <= info["wend"], True))
    opt.add(If(meet[p], end[p] - start[p] >= info["min_minutes"], True))

    # If meet, must be reachable from the starting point at 09:00
    t0_to_loc = travel[("The Castro", info["location"])]
    opt.add(If(meet[p], start[p] >= base_start + t0_to_loc, True))

# Pairwise travel-time separation between any two meetings
persons = list(friends.keys())
for i in range(len(persons)):
    for j in range(i+1, len(persons)):
        p, q = persons[i], persons[j]
        lp, lq = friends[p]["location"], friends[q]["location"]
        tpq = travel[(lp, lq)]
        tqp = travel[(lq, lp)]
        # If both are scheduled, enforce one must precede the other with travel time
        both = And(meet[p], meet[q])
        opt.add(If(both, Or(end[p] + tpq <= start[q], end[q] + tqp <= start[p]), True))

# Objectives:
# 1) Maximize number of friends met
count_met = sum(If(meet[p], 1, 0) for p in persons)
opt.maximize(count_met)

# 2) Secondary: maximize total meeting minutes
total_minutes = sum(If(meet[p], end[p] - start[p], 0) for p in persons)
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit()

m = opt.model()

# Build itinerary
schedule = []
for p in persons:
    if m.eval(meet[p]).is_true():
        s = m.eval(start[p]).as_long()
        e = m.eval(end[p]).as_long()
        schedule.append({
            "action": "meet",
            "person": p,
            "start_time": minutes_to_hm(s),
            "end_time": minutes_to_hm(e),
        })

# Sort by start time
schedule.sort(key=lambda x: hm_to_minutes(x["start_time"]))

print(json.dumps({"itinerary": schedule}))