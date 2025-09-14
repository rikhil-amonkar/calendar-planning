# SOLUTION:
from z3 import *
import json

def t(h, m):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Locations indices: 0: Embarcadero, 1: Richmond District, 2: Fisherman's Wharf
locations = ["Embarcadero", "Richmond District", "Fisherman's Wharf"]

# People indices: 0: Jessica, 1: Sandra, 2: Jason
people = [
    {"name": "Jessica", "location_idx": 0, "start": t(16, 45), "end": t(19, 0), "min": 30},
    {"name": "Sandra", "location_idx": 1, "start": t(18, 30), "end": t(21, 45), "min": 120},
    {"name": "Jason",  "location_idx": 2, "start": t(16, 0),  "end": t(16, 45), "min": 30},
]

# Travel times (minutes)
# Bayview to locations
bayview_to_loc = [19, 25, 25]  # Embarcadero, Richmond District, Fisherman's Wharf

# Between locations matrix (from row -> col)
# Embarcadero(0) to [Embarcadero, Richmond, Fisherman's]
# Richmond(1) to [...]
# Fisherman's(2) to [...]
between = [
    [0, 21, 6],
    [19, 0, 18],
    [8, 18, 0]
]

arrive_bayview = t(9, 0)

def pick_val(idx, vals):
    # vals is a list of 3 integers for idx in {0,1,2}
    assert len(vals) == 3
    e = IntVal(vals[2])
    e = If(idx == 1, IntVal(vals[1]), e)
    e = If(idx == 0, IntVal(vals[0]), e)
    return e

def travel_from_bayview(pi):
    # pi in {0,1,2}
    return pick_val(pi, bayview_to_loc)

def travel_between(prev_pi, curr_pi):
    # Returns travel time based on person indices (prev -> curr)
    row0 = pick_val(curr_pi, between[0])
    row1 = pick_val(curr_pi, between[1])
    row2 = pick_val(curr_pi, between[2])
    return If(prev_pi == 0, row0, If(prev_pi == 1, row1, row2))

# Build arrays for quick picking by person index
starts_by_person = [p["start"] for p in people]
ends_by_person = [p["end"] for p in people]
mins_by_person = [p["min"] for p in people]
loc_idx_by_person = [p["location_idx"] for p in people]

# SMT variables
active = [Bool(f"active_{i}") for i in range(3)]
p = [Int(f"p_{i}") for i in range(3)]          # person index for slot i (0..2), or 3 when inactive
start = [Int(f"start_{i}") for i in range(3)]  # minutes from midnight
end = [Int(f"end_{i}") for i in range(3)]      # minutes from midnight

opt = Optimize()
opt.set(priority='lex')

for i in range(3):
    # Domain on person selection variable
    # If active -> p in {0,1,2}; else p == 3
    opt.add(Or(And(active[i], And(p[i] >= 0, p[i] <= 2)),
               And(Not(active[i]), p[i] == 3)))
    # Times are non-negative
    opt.add(start[i] >= 0, end[i] >= 0)
    # If inactive, zero-out times for cleanliness
    opt.add(Implies(Not(active[i]), And(start[i] == 0, end[i] == 0)))
    # If active, enforce basic time ordering
    opt.add(Implies(active[i], end[i] >= start[i]))

# Contiguity: no gaps (slot i active => slot i-1 active)
opt.add(Implies(active[1], active[0]))
opt.add(Implies(active[2], active[1]))

# Distinct people across active slots
for i in range(3):
    for j in range(i + 1, 3):
        opt.add(Implies(And(active[i], active[j]), p[i] != p[j]))

# Time window and travel constraints
for i in range(3):
    # Meeting must occur within person's availability window with minimum duration
    person_start = pick_val(p[i], starts_by_person)
    person_end = pick_val(p[i], ends_by_person)
    person_min = pick_val(p[i], mins_by_person)

    opt.add(Implies(active[i], start[i] >= person_start))
    opt.add(Implies(active[i], end[i] <= person_end))
    opt.add(Implies(active[i], end[i] - start[i] >= person_min))

    # Travel constraints
    if i == 0:
        # From Bayview (arrival at 9:00)
        opt.add(Implies(active[0], start[0] >= arrive_bayview + travel_from_bayview(p[0])))
    else:
        # From previous meeting location
        opt.add(Implies(active[i], start[i] >= end[i - 1] + travel_between(p[i - 1], p[i])))

# Objective 1: maximize number of meetings
num_meetings = Sum([If(active[i], 1, 0) for i in range(3)])
opt.maximize(num_meetings)

# Objective 2: maximize total meeting time
total_meeting_time = Sum([If(active[i], end[i] - start[i], 0) for i in range(3)])
opt.maximize(total_meeting_time)

# Objective 3: minimize total travel time
travel_times = []
travel_times.append(If(active[0], travel_from_bayview(p[0]), 0))
travel_times.append(If(active[1], travel_between(p[0], p[1]), 0))
travel_times.append(If(active[2], travel_between(p[1], p[2]), 0))
total_travel_time = Sum(travel_times)
opt.minimize(total_travel_time)

if opt.check() != sat:
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    m = opt.model()
    itinerary = []
    for i in range(3):
        if is_true(m.evaluate(active[i])):
            pi = m.evaluate(p[i]).as_long()
            s = m.evaluate(start[i]).as_long()
            e = m.evaluate(end[i]).as_long()
            entry = {
                "action": "meet",
                "location": locations[loc_idx_by_person[pi]],
                "person": people[pi]["name"],
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e)
            }
            itinerary.append(entry)
    result = {"itinerary": itinerary}
    print(json.dumps(result))