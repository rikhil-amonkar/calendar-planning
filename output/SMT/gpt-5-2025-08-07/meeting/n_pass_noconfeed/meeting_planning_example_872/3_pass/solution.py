import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat, is_true

# Time utility
def to_min(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Data
start_location = "Presidio"
start_time = to_min(9, 0)  # 9:00

# Friends: name -> (location, availability_start, availability_end, min_duration)
friends = {
    "Karen":     ("Haight-Ashbury",   to_min(21, 0),  to_min(21, 45), 45),
    "Jessica":   ("Nob Hill",         to_min(13, 45), to_min(21, 0),  90),
    "Brian":     ("Russian Hill",     to_min(15, 30), to_min(21, 45), 60),
    "Kenneth":   ("North Beach",      to_min(9, 45),  to_min(21, 0),  30),
    "Jason":     ("Chinatown",        to_min(8, 15),  to_min(11, 45), 75),
    "Stephanie": ("Union Square",     to_min(14, 45), to_min(18, 45), 105),
    "Kimberly":  ("Embarcadero",      to_min(9, 45),  to_min(19, 30), 75),
    "Steven":    ("Financial District",to_min(7, 15), to_min(21, 15), 60),
    "Mark":      ("Marina District",  to_min(10, 15), to_min(13, 0),  75),
}

# Travel times (minutes) between neighborhoods
T = {}
def set_t(a, b, t):
    T.setdefault(a, {})[b] = t

# Populate travel times
set_t("Presidio", "Haight-Ashbury", 15)
set_t("Presidio", "Nob Hill", 18)
set_t("Presidio", "Russian Hill", 14)
set_t("Presidio", "North Beach", 18)
set_t("Presidio", "Chinatown", 21)
set_t("Presidio", "Union Square", 22)
set_t("Presidio", "Embarcadero", 20)
set_t("Presidio", "Financial District", 23)
set_t("Presidio", "Marina District", 11)

set_t("Haight-Ashbury", "Presidio", 15)
set_t("Haight-Ashbury", "Nob Hill", 15)
set_t("Haight-Ashbury", "Russian Hill", 17)
set_t("Haight-Ashbury", "North Beach", 19)
set_t("Haight-Ashbury", "Chinatown", 19)
set_t("Haight-Ashbury", "Union Square", 19)
set_t("Haight-Ashbury", "Embarcadero", 20)
set_t("Haight-Ashbury", "Financial District", 21)
set_t("Haight-Ashbury", "Marina District", 17)

set_t("Nob Hill", "Presidio", 17)
set_t("Nob Hill", "Haight-Ashbury", 13)
set_t("Nob Hill", "Russian Hill", 5)
set_t("Nob Hill", "North Beach", 8)
set_t("Nob Hill", "Chinatown", 6)
set_t("Nob Hill", "Union Square", 7)
set_t("Nob Hill", "Embarcadero", 9)
set_t("Nob Hill", "Financial District", 9)
set_t("Nob Hill", "Marina District", 11)

set_t("Russian Hill", "Presidio", 14)
set_t("Russian Hill", "Haight-Ashbury", 17)
set_t("Russian Hill", "Nob Hill", 5)
set_t("Russian Hill", "North Beach", 5)
set_t("Russian Hill", "Chinatown", 9)
set_t("Russian Hill", "Union Square", 10)
set_t("Russian Hill", "Embarcadero", 8)
set_t("Russian Hill", "Financial District", 11)
set_t("Russian Hill", "Marina District", 7)

set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Haight-Ashbury", 18)
set_t("North Beach", "Nob Hill", 7)
set_t("North Beach", "Russian Hill", 4)
set_t("North Beach", "Chinatown", 6)
set_t("North Beach", "Union Square", 7)
set_t("North Beach", "Embarcadero", 6)
set_t("North Beach", "Financial District", 8)
set_t("North Beach", "Marina District", 9)

set_t("Chinatown", "Presidio", 19)
set_t("Chinatown", "Haight-Ashbury", 19)
set_t("Chinatown", "Nob Hill", 9)
set_t("Chinatown", "Russian Hill", 7)
set_t("Chinatown", "North Beach", 3)
set_t("Chinatown", "Union Square", 7)
set_t("Chinatown", "Embarcadero", 5)
set_t("Chinatown", "Financial District", 5)
set_t("Chinatown", "Marina District", 12)

set_t("Union Square", "Presidio", 24)
set_t("Union Square", "Haight-Ashbury", 18)
set_t("Union Square", "Nob Hill", 9)
set_t("Union Square", "Russian Hill", 13)
set_t("Union Square", "North Beach", 10)
set_t("Union Square", "Chinatown", 7)
set_t("Union Square", "Embarcadero", 11)
set_t("Union Square", "Financial District", 9)
set_t("Union Square", "Marina District", 18)

set_t("Embarcadero", "Presidio", 20)
set_t("Embarcadero", "Haight-Ashbury", 21)
set_t("Embarcadero", "Nob Hill", 10)
set_t("Embarcadero", "Russian Hill", 8)
set_t("Embarcadero", "North Beach", 5)
set_t("Embarcadero", "Chinatown", 7)
set_t("Embarcadero", "Union Square", 10)
set_t("Embarcadero", "Financial District", 5)
set_t("Embarcadero", "Marina District", 12)

set_t("Financial District", "Presidio", 22)
set_t("Financial District", "Haight-Ashbury", 19)
set_t("Financial District", "Nob Hill", 8)
set_t("Financial District", "Russian Hill", 11)
set_t("Financial District", "North Beach", 7)
set_t("Financial District", "Chinatown", 5)
set_t("Financial District", "Union Square", 9)
set_t("Financial District", "Embarcadero", 4)
set_t("Financial District", "Marina District", 15)

set_t("Marina District", "Presidio", 10)
set_t("Marina District", "Haight-Ashbury", 16)
set_t("Marina District", "Nob Hill", 12)
set_t("Marina District", "Russian Hill", 8)
set_t("Marina District", "North Beach", 11)
set_t("Marina District", "Chinatown", 15)
set_t("Marina District", "Union Square", 16)
set_t("Marina District", "Embarcadero", 14)
set_t("Marina District", "Financial District", 17)

# Build Z3 model
opt = Optimize()
opt.set(priority='lex')  # lexicographic optimization

names = list(friends.keys())
s_vars = {}
e_vars = {}
b_vars = {}

for name in names:
    loc, a_start, a_end, dur = friends[name]
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    b = Bool(f"b_{name}")
    s_vars[name] = s
    e_vars[name] = e
    b_vars[name] = b

    # Within availability window
    opt.add(s >= a_start)
    opt.add(e <= a_end)
    opt.add(e >= s)

    # If attending, meet minimum duration; else zero-length dummy at window start
    opt.add(Implies(b, e - s >= dur))
    opt.add(Implies(~b, And(s == a_start, e == a_start)))

    # Reachable from start location at or after start time
    travel_from_start = T[start_location][loc]
    opt.add(Implies(b, s >= start_time + travel_from_start))

# Pairwise non-overlap with travel-time precedence
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni, nj = names[i], names[j]
        loci, locj = friends[ni][0], friends[nj][0]
        tij = T[loci][locj]
        tji = T[locj][loci]
        si, ei, bi = s_vars[ni], e_vars[ni], b_vars[ni]
        sj, ej, bj = s_vars[nj], e_vars[nj], b_vars[nj]
        # If both meetings happen, one must be after the other including travel time
        opt.add(Implies(And(bi, bj), Or(sj >= ei + tij, si >= ej + tji)))

# Objectives: lexicographic
total_meets = Sum([If(b_vars[n], 1, 0) for n in names])
total_minutes = Sum([If(b_vars[n], e_vars[n] - s_vars[n], 0) for n in names])

latest_end = Int("latest_end")
opt.add(latest_end >= 0)
for n in names:
    opt.add(Implies(b_vars[n], latest_end >= e_vars[n]))

opt.maximize(total_meets)
opt.maximize(total_minutes)
opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for name in names:
        if is_true(model.eval(b_vars[name], model_completion=True)):
            s_val = model.eval(s_vars[name], model_completion=True).as_long()
            e_val = model.eval(e_vars[name], model_completion=True).as_long()
            loc = friends[name][0]
            meetings.append({
                "person": name,
                "location": loc,
                "start": s_val,
                "end": e_val
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Build itinerary with travel steps
    itinerary = []
    curr_loc = start_location
    curr_time = start_time
    for m in meetings:
        # Add travel step if needed
        t_travel = T[curr_loc][m["location"]]
        depart = curr_time
        arrive = curr_time + t_travel
        itinerary.append({
            "action": "travel",
            "from": curr_loc,
            "to": m["location"],
            "depart_time": fmt_time(depart),
            "arrive_time": fmt_time(arrive),
            "minutes": t_travel
        })
        # Add meeting (may include waiting time before start)
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": fmt_time(m["start"]),
            "end_time": fmt_time(m["end"]),
            "minutes": m["end"] - m["start"]
        })
        curr_loc = m["location"]
        curr_time = m["end"]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))