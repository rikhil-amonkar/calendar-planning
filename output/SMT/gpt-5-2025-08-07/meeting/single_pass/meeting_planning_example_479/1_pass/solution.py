# Z3-based optimizer to maximize number of friends met subject to travel and availability constraints.
# Prints a JSON itinerary with the chosen meetings.

from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat
import json

def t(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return hh * 60 + mm

def fmt(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Data
start_loc = "Embarcadero"
start_time = t("09:00")

# Travel times (directed, minutes)
T = {
    "Embarcadero": {
        "Golden Gate Park": 25, "Haight-Ashbury": 21, "Bayview": 21, "Presidio": 20, "Financial District": 5
    },
    "Golden Gate Park": {
        "Embarcadero": 25, "Haight-Ashbury": 7, "Bayview": 23, "Presidio": 11, "Financial District": 26
    },
    "Haight-Ashbury": {
        "Embarcadero": 20, "Golden Gate Park": 7, "Bayview": 18, "Presidio": 15, "Financial District": 21
    },
    "Bayview": {
        "Embarcadero": 19, "Golden Gate Park": 22, "Haight-Ashbury": 19, "Presidio": 31, "Financial District": 19
    },
    "Presidio": {
        "Embarcadero": 20, "Golden Gate Park": 12, "Haight-Ashbury": 15, "Bayview": 31, "Financial District": 23
    },
    "Financial District": {
        "Embarcadero": 4, "Golden Gate Park": 23, "Haight-Ashbury": 19, "Bayview": 19, "Presidio": 22
    },
}

# People: name -> dict with location, availability window, and required duration
people = {
    "Mary":      {"loc": "Golden Gate Park",    "avail": (t("08:45"), t("11:45")), "dur": 45},
    "Kevin":     {"loc": "Haight-Ashbury",      "avail": (t("10:15"), t("16:15")), "dur": 90},
    "Deborah":   {"loc": "Bayview",             "avail": (t("15:00"), t("19:15")), "dur": 120},
    "Stephanie": {"loc": "Presidio",            "avail": (t("10:00"), t("17:15")), "dur": 120},
    "Emily":     {"loc": "Financial District",  "avail": (t("11:30"), t("21:45")), "dur": 105},
}

names = list(people.keys())

opt = Optimize()

# Decision variables
meet = {n: Bool(f"meet_{n}") for n in names}
start = {n: Int(f"start_{n}") for n in names}
end   = {n: Int(f"end_{n}")   for n in names}

# Availability and duration constraints
for n in names:
    s, e = start[n], end[n]
    a0, a1 = people[n]["avail"]
    dur = people[n]["dur"]

    # If meeting, respect availability and duration; if not, set end==start (no time consumed)
    opt.add(If(meet[n], And(s >= a0, e <= a1, e == s + dur), e == s))

    # Non-negative times
    opt.add(s >= 0, e >= 0)

    # Reachability from start (conservative lower bound on first possible start)
    loc = people[n]["loc"]
    opt.add(If(meet[n], s >= start_time + T[start_loc][loc], True))

# Pairwise ordering constraints with travel times
order = {}
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        oi = people[ni]["loc"]
        oj = people[nj]["loc"]
        oij = Bool(f"order_{ni}_before_{nj}")  # True if i before j when both met
        order[(ni, nj)] = oij

        # If both are met, enforce that either i is before j with enough travel time,
        # or j is before i with enough travel time.
        # Implemented by two implications guarded by the order boolean.
        opt.add(If(And(meet[ni], meet[nj], oij),
                   start[nj] >= end[ni] + T[oi][oj],
                   True))
        opt.add(If(And(meet[ni], meet[nj], Not(oij)),
                   start[ni] >= end[nj] + T[oj][oi],
                   True))

        # If either isn't met, order variable is irrelevant; no extra constraint needed.

# Objective: maximize number of friends met
opt.maximize(Sum([If(meet[n], 1, 0) for n in names]))

# Optional tie-breakers to get earlier, tidy schedules (not required for correctness)
# 1) Minimize total end time (makespan upper bound)
makespan = Int("makespan")
opt.add(makespan >= start_time)
for n in names:
    opt.add(makespan >= end[n])
opt.minimize(makespan)

# 2) Minimize sum of start times (prefers earlier starts when tied)
opt.minimize(Sum([If(meet[n], start[n], 0) for n in names]))

res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit(0)

m = opt.model()

meetings = []
for n in names:
    if m.evaluate(meet[n]).is_true():
        s = m.evaluate(start[n]).as_long()
        e = m.evaluate(end[n]).as_long()
        meetings.append({
            "action": "meet",
            "person": n,
            "start_time": fmt(s),
            "end_time": fmt(e),
        })

# Sort by start time
meetings.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": meetings}))