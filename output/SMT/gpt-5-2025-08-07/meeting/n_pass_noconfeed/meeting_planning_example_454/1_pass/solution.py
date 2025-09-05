"""SOLUTION:"""
from z3 import *
import json

# Helper functions
def t(h, m=0):
    return h * 60 + m

def minutes_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Presidio",
    "Golden Gate Park",
    "Bayview",
    "Chinatown",
    "North Beach",
    "Mission District",
]

# Travel times (minutes)
tt = {}
def add(a, b, minutes):
    tt[(a, b)] = minutes

add("Presidio", "Golden Gate Park", 12)
add("Presidio", "Bayview", 31)
add("Presidio", "Chinatown", 21)
add("Presidio", "North Beach", 18)
add("Presidio", "Mission District", 26)

add("Golden Gate Park", "Presidio", 11)
add("Golden Gate Park", "Bayview", 23)
add("Golden Gate Park", "Chinatown", 23)
add("Golden Gate Park", "North Beach", 24)
add("Golden Gate Park", "Mission District", 17)

add("Bayview", "Presidio", 31)
add("Bayview", "Golden Gate Park", 22)
add("Bayview", "Chinatown", 18)
add("Bayview", "North Beach", 21)
add("Bayview", "Mission District", 13)

add("Chinatown", "Presidio", 19)
add("Chinatown", "Golden Gate Park", 23)
add("Chinatown", "Bayview", 22)
add("Chinatown", "North Beach", 3)
add("Chinatown", "Mission District", 18)

add("North Beach", "Presidio", 17)
add("North Beach", "Golden Gate Park", 22)
add("North Beach", "Bayview", 22)
add("North Beach", "Chinatown", 6)
add("North Beach", "Mission District", 18)

add("Mission District", "Presidio", 25)
add("Mission District", "Golden Gate Park", 17)
add("Mission District", "Bayview", 15)
add("Mission District", "Chinatown", 16)
add("Mission District", "North Beach", 17)

# Friends data
friends = [
    {"person": "Jessica", "location": "Golden Gate Park", "avail": (t(13,45), t(15,0)), "min_dur": 30},
    {"person": "Ashley", "location": "Bayview", "avail": (t(17,15), t(20,0)), "min_dur": 105},
    {"person": "Ronald", "location": "Chinatown", "avail": (t(7,15), t(14,45)), "min_dur": 90},
    {"person": "William", "location": "North Beach", "avail": (t(13,15), t(20,15)), "min_dur": 15},
    {"person": "Daniel", "location": "Mission District", "avail": (t(7,0), t(11,15)), "min_dur": 105},
]

n = len(friends)
positions = list(range(n))  # 0..4

start_at = t(9, 0)
start_location = "Presidio"

opt = Optimize()

# Decision variables
selected = [Bool(f"selected_{i}") for i in range(n)]
start_time = [Int(f"start_{i}") for i in range(n)]
end_time = [Int(f"end_{i}") for i in range(n)]

# Position assignment variables x[k][i]: meeting i is at position k
x = [[Bool(f"x_{k}_{i}") for i in range(n)] for k in positions]
# Position used flags
is_used = [Bool(f"is_used_{k}") for k in positions]
M = Int("M")  # number of meetings scheduled

# Time bounds and availability constraints
for i, f in enumerate(friends):
    s = start_time[i]
    e = end_time[i]
    a_start, a_end = f["avail"]
    min_dur = f["min_dur"]
    # Bounds
    opt.add(s >= 0, e >= 0, s <= t(23,59), e <= t(23,59))
    # If selected -> enforce availability and duration
    opt.add(Implies(selected[i], And(s >= a_start, e <= a_end, e - s >= min_dur)))
    # If not selected -> no duration (degenerate)
    opt.add(Implies(Not(selected[i]), e == s))

# Position and contiguity constraints
# Each meeting assigned to exactly one position iff selected
for i in range(n):
    opt.add(Sum([If(x[k][i], 1, 0) for k in positions]) == If(selected[i], 1, 0))

# Each position has at most one meeting; equals 1 iff used
for k in positions:
    opt.add(Sum([If(x[k][i], 1, 0) for i in range(n)]) == If(is_used[k], 1, 0))

# Contiguous used positions: prefix of True followed by False
for k in range(n - 1):
    opt.add(Implies(is_used[k + 1], is_used[k]))

# M equals number of used positions and number of selected meetings
opt.add(M == Sum([If(is_used[k], 1, 0) for k in positions]))
opt.add(M == Sum([If(selected[i], 1, 0) for i in range(n)]))
opt.add(M >= 0, M <= n)

# Travel and sequencing constraints
# First position: from start location at 9:00
for i, f in enumerate(friends):
    travel0 = tt[(start_location, f["location"])]
    opt.add(Implies(And(is_used[0], x[0][i]), start_time[i] >= start_at + travel0))

# Transitions between consecutive positions
for k in range(n - 1):
    for i, fi in enumerate(friends):
        for j, fj in enumerate(friends):
            if i == j:
                # Can't have same meeting in adjacent positions
                opt.add(Implies(And(x[k][i], x[k+1][j]), False))
                continue
            travel_ij = tt[(fi["location"], fj["location"])]
            opt.add(
                Implies(
                    And(is_used[k], is_used[k + 1], x[k][i], x[k + 1][j]),
                    start_time[j] >= end_time[i] + travel_ij
                )
            )

# Ensure uniqueness: no meeting appears in two positions (already enforced), and positions don't have duplicates (enforced)

# Objective: maximize number of friends met, then maximize total meeting time
total_met = Sum([If(selected[i], 1, 0) for i in range(n)])
total_minutes = Sum([If(selected[i], end_time[i] - start_time[i], 0) for i in range(n)])
opt.maximize(total_met)
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    # If unsat (shouldn't happen), output empty itinerary
    output = {"itinerary": []}
    print(json.dumps(output))
    exit(0)

m = opt.model()

# Build itinerary in order of positions
itinerary = []
used_positions = [is_true(m.evaluate(is_used[k])) for k in positions]
for k in positions:
    if not used_positions[k]:
        break
    chosen_i = None
    for i in range(n):
        if is_true(m.evaluate(x[k][i])):
            chosen_i = i
            break
    if chosen_i is None:
        continue
    s = m.evaluate(start_time[chosen_i]).as_long()
    e = m.evaluate(end_time[chosen_i]).as_long()
    itinerary.append({
        "action": "meet",
        "location": friends[chosen_i]["location"],
        "person": friends[chosen_i]["person"],
        "start_time": minutes_to_str(s),
        "end_time": minutes_to_str(e)
    })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))