import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum

# Helper to convert "H:MM" 24-hour strings to minutes since midnight
def tmin(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

# Helper to convert minutes since midnight to "H:MM" 24-hour format without leading zero
def tstr(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes) between locations, asymmetric as given
dist = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}
# Ensure dist[loc][loc] = 0 for all locations
for a in dist.keys():
    dist[a][a] = 0

# Friends data: name, location, availability window (24h), minimum meeting duration
friends = [
    {"name": "Stephanie", "location": "Fisherman's Wharf", "avail": ("15:30", "22:00"), "min": 30},
    {"name": "Lisa", "location": "Financial District", "avail": ("10:45", "17:15"), "min": 15},
    {"name": "Melissa", "location": "Russian Hill", "avail": ("17:00", "21:45"), "min": 120},
    {"name": "Betty", "location": "Marina District", "avail": ("10:45", "14:15"), "min": 60},
    {"name": "Sarah", "location": "Richmond District", "avail": ("16:15", "19:30"), "min": 105},
    {"name": "Daniel", "location": "Pacific Heights", "avail": ("18:30", "21:45"), "min": 60},
    {"name": "Joshua", "location": "Haight-Ashbury", "avail": ("9:00", "15:30"), "min": 15},
    {"name": "Joseph", "location": "Presidio", "avail": ("7:00", "13:00"), "min": 45},
    {"name": "Andrew", "location": "Nob Hill", "avail": ("19:45", "22:00"), "min": 105},
    {"name": "John", "location": "The Castro", "avail": ("13:15", "19:45"), "min": 45}
]

day_start_loc = "Embarcadero"
day_start_time = tmin("9:00")

# Build Z3 model
opt = Optimize()
opt.set(priority='lex')

s_vars = {}
e_vars = {}
dur_vars = {}
sel_vars = {}

# Create variables and basic constraints
for f in friends:
    name = f["name"]
    avail_s = tmin(f["avail"][0])
    avail_e = tmin(f["avail"][1])
    min_d = f["min"]

    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    d = Int(f"d_{name}")
    sel = Bool(f"sel_{name}")

    s_vars[name] = s
    e_vars[name] = e
    dur_vars[name] = d
    sel_vars[name] = sel

    # Duration definition
    opt.add(d == e - s)
    opt.add(d >= 0)

    # Availability window constraints when selected
    opt.add(If(sel, s >= avail_s, s == avail_s))
    opt.add(If(sel, e <= avail_e, e == avail_s))
    opt.add(If(sel, d >= min_d, d == 0))

    # Must be able to reach from start location
    travel_from_start = dist[day_start_loc][f["location"]]
    opt.add(If(sel, s >= day_start_time + travel_from_start, True))

# Pairwise ordering and travel non-overlap constraints
n = len(friends)
before_bools = {}
for i in range(n):
    for j in range(i+1, n):
        fi = friends[i]
        fj = friends[j]
        ni = fi["name"]
        nj = fj["name"]
        bi_j = Bool(f"before_{ni}_then_{nj}")
        before_bools[(ni, nj)] = bi_j

        # If both are selected and i before j, then j starts after i ends plus travel
        travel_ij = dist[fi["location"]][fj["location"]]
        travel_ji = dist[fj["location"]][fi["location"]]

        opt.add(
            If(And(sel_vars[ni], sel_vars[nj], bi_j),
               s_vars[nj] >= e_vars[ni] + travel_ij,
               True)
        )
        # If both selected and j before i (i.e., not bi_j), then i starts after j ends plus travel
        opt.add(
            If(And(sel_vars[ni], sel_vars[nj], Not(bi_j)),
               s_vars[ni] >= e_vars[nj] + travel_ji,
               True)
        )

# Objective 1: maximize number of friends met
total_met = Sum([If(sel_vars[f["name"]], 1, 0) for f in friends])
opt.maximize(total_met)

# Objective 2: maximize total meeting time (lexicographic secondary)
total_minutes = Sum([dur_vars[f["name"]] for f in friends])
opt.maximize(total_minutes)

# Solve
result = opt.check()
itinerary = []

if str(result) == "sat":
    m = opt.model()
    # Collect selected meetings with concrete times
    meetings = []
    for f in friends:
        name = f["name"]
        if m.evaluate(sel_vars[name]):
            start = m.evaluate(s_vars[name]).as_long()
            end = m.evaluate(e_vars[name]).as_long()
            meetings.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time_min": start,
                "end_time_min": end
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start_time_min"])
    # Format times
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": tstr(mt["start_time_min"]),
            "end_time": tstr(mt["end_time_min"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))