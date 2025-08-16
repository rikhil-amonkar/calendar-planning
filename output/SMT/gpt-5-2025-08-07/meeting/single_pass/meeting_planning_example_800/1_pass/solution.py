# Solve the SF day-planning problem with Z3 to maximize the number of friends met.
# The model enforces:
# - Meeting windows and minimum durations
# - Travel times between any two selected meetings (disjunctive sequencing)
# - Start at Union Square at 09:00 and obey travel to the first meeting
# It then prints one optimal itinerary as JSON.

from z3 import Optimize, Int, Bool, And, Or, Not, If, Sum
import json

# Minutes helper
def hm_to_min(h, m):
    return h * 60 + m

def min_to_hhmm(x):
    h = x // 60
    m = x % 60
    return f"{h:02d}:{m:02d}"

# Locations
US = "Union Square"
locs = [
    "Union Square",
    "The Castro",
    "North Beach",
    "Embarcadero",
    "Alamo Square",
    "Nob Hill",
    "Presidio",
    "Fisherman's Wharf",
    "Mission District",
    "Haight-Ashbury",
]

# Travel times (minutes), as given (directional)
T = {
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14,
        "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7,
        "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18,
        "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19,
        "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20,
        "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16,
        "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10,
        "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9,
        "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13,
        "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20,
        "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26,
        "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8,
        "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22,
        "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19,
        "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20,
        "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23,
        "Mission District": 11
    }
}

# People data: location, window [start, end], min duration (minutes)
people = {
    "Melissa":  {"loc": "The Castro",         "win": (hm_to_min(20,15), hm_to_min(21,15)), "min": 30},
    "Kimberly": {"loc": "North Beach",        "win": (hm_to_min(7,0),   hm_to_min(10,30)), "min": 15},
    "Joseph":   {"loc": "Embarcadero",        "win": (hm_to_min(15,30), hm_to_min(19,30)), "min": 75},
    "Barbara":  {"loc": "Alamo Square",       "win": (hm_to_min(20,45), hm_to_min(21,45)), "min": 15},
    "Kenneth":  {"loc": "Nob Hill",           "win": (hm_to_min(12,15), hm_to_min(17,15)), "min": 105},
    "Joshua":   {"loc": "Presidio",           "win": (hm_to_min(16,30), hm_to_min(18,15)), "min": 105},
    "Brian":    {"loc": "Fisherman's Wharf",  "win": (hm_to_min(9,30),  hm_to_min(15,30)), "min": 45},
    "Steven":   {"loc": "Mission District",   "win": (hm_to_min(19,30), hm_to_min(21,0)),  "min": 90},
    "Betty":    {"loc": "Haight-Ashbury",     "win": (hm_to_min(19,0),  hm_to_min(20,30)), "min": 90},
}

start_time = hm_to_min(9, 0)  # 09:00 at Union Square

# Z3 model
opt = Optimize()

s_vars = {}
e_vars = {}
meet_vars = {}

# Create variables and basic constraints
for name, data in people.items():
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    m = Bool(f"meet_{name}")
    s_vars[name] = s
    e_vars[name] = e
    meet_vars[name] = m

    w0, w1 = data["win"]
    min_dur = data["min"]

    # Domains
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)

    # If meet, respect window and duration; if not, pin to window start for determinism
    opt.add(Or(Not(m), And(s >= w0, e <= w1, e - s >= min_dur)))
    opt.add(Or(m, And(s == w0, e == w0)))

    # Start-from-Union-Square travel constraint for first meeting
    # If you meet them at all, you cannot start earlier than 09:00 + travel(US->loc)
    opt.add(Or(Not(m), s >= start_time + T[US][data["loc"]]))

# Disjunctive sequencing with travel times between any two meetings
names = list(people.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        li, lj = people[ni]["loc"], people[nj]["loc"]
        ti_j = T[li][lj]
        tj_i = T[lj][li]
        si, ei, mi = s_vars[ni], e_vars[ni], meet_vars[ni]
        sj, ej, mj = s_vars[nj], e_vars[nj], meet_vars[nj]
        # If both are met, either j is after i with travel, or i is after j with travel
        opt.add(Or(Not(mi), Not(mj), sj >= ei + ti_j, si >= ej + tj_i))

# Objective: maximize the number of friends met
meet_count = Sum([If(meet_vars[n], 1, 0) for n in names])
opt.maximize(meet_count)

# Optionally add slight preferences to break ties toward a nice evening cluster (Betty+Melissa+Barbara)
# but keep the primary objective purely on count.
pref_weight = Sum([
    If(meet_vars["Betty"], 1, 0),
    If(meet_vars["Melissa"], 1, 0),
    If(meet_vars["Barbara"], 1, 0)
])
opt.maximize(pref_weight)

res = opt.check()
assert str(res) == "sat", "No feasible itinerary found."

model = opt.model()

# Extract and sort meetings by start time
meetings = []
for name in names:
    if model.eval(meet_vars[name], model_completion=True):
        s = model.eval(s_vars[name]).as_long()
        e = model.eval(e_vars[name]).as_long()
        meetings.append((s, e, name))

meetings.sort(key=lambda x: x[0])

itinerary = []
for s, e, name in meetings:
    itinerary.append({
        "action": "meet",
        "person": name,
        "start_time": min_to_hhmm(s),
        "end_time": min_to_hhmm(e)
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))