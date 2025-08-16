# Z3-based solver for the described scheduling problem.
# Goal: maximize time with Robert while respecting travel and availability constraints.

from z3 import Optimize, Int, sat
import json

def minutes_to_hhmm(m):
    h = m // 60
    n = m % 60
    return f"{h:02d}:{n:02d}"

# Constants (times in minutes since midnight)
ARRIVE_NOB_HILL = 9 * 60                     # 09:00 -> 540
NH_TO_PRESIDIO = 17                          # minutes
ROBERT_START = 11 * 60 + 15                  # 11:15 -> 675
ROBERT_END = 17 * 60 + 45                    # 17:45 -> 1065
MIN_MEET_MINUTES = 120

# Z3 variables
dep_NH = Int("dep_NH")       # departure time from Nob Hill
arr_P = Int("arr_P")         # arrival time at Presidio
start = Int("start")         # meeting start time
end = Int("end")             # meeting end time
dur = Int("dur")             # meeting duration

opt = Optimize()

# Domain bounds for safety
for v in [dep_NH, arr_P, start, end, dur]:
    opt.add(v >= 0, v <= 24 * 60)

# Travel and timing constraints
opt.add(dep_NH >= ARRIVE_NOB_HILL)
opt.add(arr_P == dep_NH + NH_TO_PRESIDIO)

# Meeting must be within Robert's availability and after arrival
opt.add(start >= arr_P)
opt.add(start >= ROBERT_START)
opt.add(end <= ROBERT_END)
opt.add(end >= start)

# Duration constraints
opt.add(dur == end - start)
opt.add(dur >= MIN_MEET_MINUTES)

# Objective: maximize meeting duration
opt.maximize(dur)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found under given constraints.")

m = opt.model()
start_val = m[start].as_long()
end_val = m[end].as_long()

itinerary = {
    "itinerary": [
        {
            "action": "meet",
            "person": "Robert",
            "start_time": minutes_to_hhmm(start_val),
            "end_time": minutes_to_hhmm(end_val),
        }
    ]
}

# Print the JSON itinerary
print(json.dumps(itinerary))