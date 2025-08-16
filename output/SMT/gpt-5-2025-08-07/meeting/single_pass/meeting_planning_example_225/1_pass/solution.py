# Z3-based optimizer for the San Francisco day schedule
# Goal: maximize number of friends met subject to availability and travel constraints.
# Secondary: minimize the latest end time to prefer earlier-finish itineraries among ties.

from z3 import *
import json

# Time helpers
def hm_to_min(h, m):
    return h * 60 + m

def min_to_hm_str(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Data
START_LOC = "Sunset District"
ARRIVAL_TIME = hm_to_min(9, 0)

travel = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,

    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,

    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,

    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

people = {
    "Sarah":   {"loc": "North Beach",  "avail_start": hm_to_min(16, 0), "avail_end": hm_to_min(18, 15), "min_dur": 60},
    "Jeffrey": {"loc": "Union Square", "avail_start": hm_to_min(15, 0), "avail_end": hm_to_min(22, 0),  "min_dur": 75},
    "Brian":   {"loc": "Alamo Square","avail_start": hm_to_min(16, 0), "avail_end": hm_to_min(17, 30), "min_dur": 75},
}

# Z3 Variables
opt = Optimize()
opt.set(priority='lex')  # maximize count first, then minimize latest end

b = {}       # whether to meet person
start = {}   # meeting start time in minutes
end = {}     # meeting end time in minutes (start + duration)

for name, info in people.items():
    b[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    end[name] = Int(f"end_{name}")
    dur = info["min_dur"]

    # If meeting, it must fit within availability
    opt.add(Implies(b[name], And(
        start[name] >= info["avail_start"],
        start[name] <= info["avail_end"] - dur,
        end[name] == start[name] + dur
    )))
    # If not meeting, allow end to be anything consistent with start + dur to keep terms well-defined
    opt.add(Implies(Not(b[name]), end[name] == start[name] + dur))

    # Must be reachable from Sunset if we choose to meet (earliest possible arrival)
    # This is a benign lower bound and does not affect feasibility for later meetings.
    s2i = travel[(START_LOC, info["loc"])]
    opt.add(Implies(b[name], start[name] >= ARRIVAL_TIME + s2i))

# Non-overlap with travel time between any two scheduled meetings
names = list(people.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni = names[i]; nj = names[j]
        li = people[ni]["loc"]; lj = people[nj]["loc"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        opt.add(Implies(And(b[ni], b[nj]),
                        Or(end[ni] + tij <= start[nj],
                           end[nj] + tji <= start[ni])))

# Objective 1: maximize number of friends met
count_met = Sum([If(b[name], 1, 0) for name in names])
opt.maximize(count_met)

# Objective 2: minimize the latest end time among scheduled meetings
M = 24 * 60  # a large constant (1 day)
latest_end = Int("latest_end")
opt.add(latest_end >= 0)
for name in names:
    # latest_end >= end[name] if b[name] is True, otherwise relaxed by big-M
    opt.add(latest_end >= end[name] - (1 - If(b[name], 1, 0)) * M)
opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")

model = opt.model()

# Build itinerary
itinerary = []
for name in names:
    if is_true(model[b[name]]):
        s = model[start[name]].as_long()
        e = model[end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": min_to_hm_str(s),
            "end_time": min_to_hm_str(e),
        })

# Sort by start time
itinerary.sort(key=lambda x: x["start_time"])

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))