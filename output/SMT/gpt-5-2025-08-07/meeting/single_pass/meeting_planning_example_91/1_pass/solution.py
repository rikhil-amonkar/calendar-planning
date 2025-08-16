# Z3-based scheduler for meeting Daniel in San Francisco
# Constraints:
# - Arrive at Russian Hill at 09:00 (540 minutes)
# - Travel times: Russian Hill -> Richmond District: 14 minutes; Richmond District -> Russian Hill: 13 minutes
# - Daniel available at Richmond District from 19:00 (1140) to 20:15 (1215)
# - Want to meet Daniel for at least 75 minutes and maximize meeting length
# Objective: maximize meeting time, then prefer earliest start time

from z3 import Optimize, Int, And, Or, If
import json

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Constants
ARRIVE_RH = 9 * 60  # 09:00 at Russian Hill
RH_to_RD = 14
RD_to_RH = 13  # Not strictly needed for this single meeting
DANIEL_START = 19 * 60  # 19:00
DANIEL_END = 20 * 60 + 15  # 20:15
MIN_MEET = 75

opt = Optimize()

# Decision variables (minutes from midnight)
start = Int('start')     # meeting start time at Richmond District
end = Int('end')         # meeting end time at Richmond District
depart = Int('depart')   # departure time from Russian Hill to Richmond District
arrive = Int('arrive')   # arrival time at Richmond District

# Time domain bounds for safety
opt.add(start >= 0, start <= 24*60)
opt.add(end >= 0, end <= 24*60)
opt.add(depart >= 0, depart <= 24*60)
opt.add(arrive >= 0, arrive <= 24*60)

# Availability window for Daniel
opt.add(start >= DANIEL_START)
opt.add(end <= DANIEL_END)

# Meeting duration constraints
opt.add(end - start >= MIN_MEET)

# Travel feasibility: can leave Russian Hill at/after arrival, travel 14 min to RD, arrive by meeting start
opt.add(depart >= ARRIVE_RH)
opt.add(arrive == depart + RH_to_RD)
opt.add(arrive <= start)

# Optimize: maximize duration, then minimize start time (earliest possible within tie)
h1 = opt.maximize(end - start)
h2 = opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found under given constraints.")

m = opt.model()
start_v = m[start].as_long()
end_v = m[end].as_long()

# Build itinerary JSON
itinerary = [{
    "action": "meet",
    "person": "Daniel",
    "start_time": minutes_to_hhmm(start_v),
    "end_time": minutes_to_hhmm(end_v)
}]

print(json.dumps({"itinerary": itinerary}))