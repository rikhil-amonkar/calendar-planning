# Solve the SF friend-meeting scheduling problem with Z3
# Goal: maximize the number of friends met while respecting availability,
# minimum meeting durations, and asymmetric travel times (including from start).

from z3 import Optimize, Int, Bool, If, Or, And, Sum
import json

def hm(h, m):
    return h * 60 + m

def m2hm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Locations
GGP = "Golden Gate Park"
FW = "Fisherman's Wharf"
BV = "Bayview"
MS = "Mission District"
EM = "Embarcadero"
FD = "Financial District"

# Travel times (minutes), as given (asymmetric)
dist = {
    (GGP, FW): 24, (GGP, BV): 23, (GGP, MS): 17, (GGP, EM): 25, (GGP, FD): 26,
    (FW, GGP): 25, (FW, BV): 26, (FW, MS): 22, (FW, EM): 8,  (FW, FD): 11,
    (BV, GGP): 22, (BV, FW): 25, (BV, MS): 13, (BV, EM): 19, (BV, FD): 19,
    (MS, GGP): 17, (MS, FW): 22, (MS, BV): 15, (MS, EM): 19, (MS, FD): 17,
    (EM, GGP): 25, (EM, FW): 6,  (EM, BV): 21, (EM, MS): 20, (EM, FD): 5,
    (FD, GGP): 23, (FD, FW): 10, (FD, BV): 19, (FD, MS): 17, (FD, EM): 4,
}

# People data: name, location, availability window, minimum duration
people = [
    {"name": "Joseph",  "loc": FW, "avail_start": hm(8, 0),  "avail_end": hm(17, 30), "min_dur": 90},
    {"name": "Jeffrey", "loc": BV, "avail_start": hm(17,30), "avail_end": hm(21, 30), "min_dur": 60},
    {"name": "Kevin",   "loc": MS, "avail_start": hm(11,15), "avail_end": hm(15, 15), "min_dur": 30},
    {"name": "David",   "loc": EM, "avail_start": hm(8,15),  "avail_end": hm(9,   0), "min_dur": 30},
    {"name": "Barbara", "loc": FD, "avail_start": hm(10,30), "avail_end": hm(16, 30), "min_dur": 15},
]

day_start_loc = GGP
day_start_time = hm(9, 0)

opt = Optimize()

# Variables
start = {}
end = {}
meet = {}

for p in people:
    name = p["name"]
    start[name] = Int(f"start_{name}")
    end[name]   = Int(f"end_{name}")
    meet[name]  = Bool(f"meet_{name}")

    # Basic domains
    opt.add(start[name] >= 0, start[name] <= 24*60)
    opt.add(end[name]   >= 0, end[name]   <= 24*60)

    # If meet -> within availability and min duration; otherwise start=end=0
    opt.add(
        If(
            meet[name],
            And(
                start[name] >= p["avail_start"],
                end[name]   <= p["avail_end"],
                end[name] - start[name] >= p["min_dur"],
                # Must be reachable from the day's start
                start[name] >= day_start_time + dist[(day_start_loc, p["loc"])]
            ),
            And(start[name] == 0, end[name] == 0)
        )
    )

# Pairwise non-overlap with travel time in either direction
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        ti = dist[(pi["loc"], pj["loc"])]
        tj = dist[(pj["loc"], pi["loc"])]
        opt.add(
            Or(
                # i before j
                end[ni] + ti <= start[nj],
                # j before i
                end[nj] + tj <= start[ni],
                # or someone not met
                Not(meet[ni]),
                Not(meet[nj])
            )
        )

# Objectives:
# 1) Maximize the number of friends met
count_met = Sum([If(meet[p["name"]], 1, 0) for p in people])
h1 = opt.maximize(count_met)
# 2) Maximize total meeting time (tie-breaker to prefer longer hangs)
total_meeting_time = Sum([If(meet[p["name"]], end[p["name"]] - start[p["name"]], 0) for p in people])
h2 = opt.maximize(total_meeting_time)
# 3) As a subtle tie-breaker, minimize latest end time to avoid very late schedules
latest_end = Int("latest_end")
opt.add(latest_end >= 0, latest_end <= 24*60)
for p in people:
    name = p["name"]
    # latest_end >= end[name] if met, else >= 0
    opt.add(latest_end >= If(meet[name], end[name], 0))
h3 = opt.minimize(latest_end)

if opt.check() != 1:
    raise RuntimeError("No solution found")

m = opt.model()

# Build itinerary
itinerary = []
for p in people:
    name = p["name"]
    if m.eval(meet[name]):
        s = m.eval(start[name]).as_long()
        e = m.eval(end[name]).as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": m2hm(s),
            "end_time": m2hm(e),
        })

# Sort by start time
itinerary.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": itinerary}, indent=2))