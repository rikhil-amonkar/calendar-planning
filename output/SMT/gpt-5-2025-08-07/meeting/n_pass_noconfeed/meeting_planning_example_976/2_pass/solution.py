import json
from z3 import Optimize, Int, Bool, If, And, Or, Xor, Implies, Sum, is_true, sat

def time_to_minutes(h, m, ampm):
    # h: 1-12, m: 0-59, ampm: 'AM' or 'PM'
    if ampm.upper() == 'AM':
        hour = 0 if h == 12 else h
    else:
        hour = 12 if h == 12 else h + 12
    return hour * 60 + m

def parse_time_label(label):
    # Examples: '7:15PM', '10:00AM'
    label = label.strip().upper()
    ampm = 'AM' if label.endswith('AM') else 'PM'
    hm = label[:-2]
    h, m = hm.split(':')
    return time_to_minutes(int(h), int(m), ampm)

def minutes_to_str24(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times matrix (minutes)
travel = {
    "Embarcadero": {
        "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20,
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12, "Embarcadero": 0
    },
    "Bayview": {
        "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32,
        "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27, "Bayview": 0
    },
    "Chinatown": {
        "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19,
        "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12, "Chinatown": 0
    },
    "Alamo Square": {
        "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17,
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15, "Alamo Square": 0
    },
    "Nob Hill": {
        "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17,
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11, "Nob Hill": 0
    },
    "Presidio": {
        "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18,
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11, "Presidio": 0
    },
    "Union Square": {
        "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9,
        "Presidio": 24, "The Castro": 17, "North Beach": 10, "Fisherman's Wharf": 15, "Marina District": 18, "Union Square": 0
    },
    "The Castro": {
        "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16,
        "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 24, "Marina District": 21, "The Castro": 0
    },
    "North Beach": {
        "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7,
        "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9, "North Beach": 0
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11,
        "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 9, "Fisherman's Wharf": 0
    },
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12,
        "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10, "Marina District": 0
    }
}

# People, locations, availability windows, and minimum meeting durations
people = [
    {"name": "Matthew", "location": "Bayview", "start": parse_time_label("7:15PM"), "end": parse_time_label("10:00PM"), "min": 120},
    {"name": "Karen", "location": "Chinatown", "start": parse_time_label("7:15PM"), "end": parse_time_label("9:15PM"), "min": 90},
    {"name": "Sarah", "location": "Alamo Square", "start": parse_time_label("8:00PM"), "end": parse_time_label("9:45PM"), "min": 105},
    {"name": "Jessica", "location": "Nob Hill", "start": parse_time_label("4:30PM"), "end": parse_time_label("6:45PM"), "min": 120},
    {"name": "Stephanie", "location": "Presidio", "start": parse_time_label("7:30AM"), "end": parse_time_label("10:15AM"), "min": 60},
    {"name": "Mary", "location": "Union Square", "start": parse_time_label("4:45PM"), "end": parse_time_label("9:30PM"), "min": 60},
    {"name": "Charles", "location": "The Castro", "start": parse_time_label("4:30PM"), "end": parse_time_label("10:00PM"), "min": 105},
    {"name": "Nancy", "location": "North Beach", "start": parse_time_label("2:45PM"), "end": parse_time_label("8:00PM"), "min": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start": parse_time_label("1:30PM"), "end": parse_time_label("7:00PM"), "min": 30},
    {"name": "Brian", "location": "Marina District", "start": parse_time_label("12:15PM"), "end": parse_time_label("6:00PM"), "min": 60},
]

# Start location and time
start_location = "Embarcadero"
start_time = parse_time_label("9:00AM")

# Z3 model
opt = Optimize()
M_big = 20000

# Variables
s = {}  # start times (minutes)
d = {}  # durations (minutes)
b = {}  # meet binary
index = {p["name"]: i for i, p in enumerate(people)}

for p in people:
    pid = p["name"]
    s[pid] = Int(f"s_{pid}")
    d[pid] = Int(f"d_{pid}")
    b[pid] = Bool(f"b_{pid}")

    # General bounds
    opt.add(s[pid] >= 0, s[pid] <= 24*60)
    opt.add(d[pid] >= 0, d[pid] <= 24*60)

    # If meeting, stay within availability window
    opt.add(s[pid] >= If(b[pid], p["start"], 0))
    opt.add(s[pid] + d[pid] <= If(b[pid], p["end"], 24*60))

    # Durations: at least min if meeting, zero otherwise; and cannot exceed window length
    window_len = p["end"] - p["start"]
    opt.add(d[pid] >= If(b[pid], p["min"], 0))
    opt.add(d[pid] <= If(b[pid], window_len, 0))

    # Must be able to get from start location to their location if meeting
    travel_from_start = travel[start_location][p["location"]]
    opt.add(s[pid] >= start_time + travel_from_start - M_big * If(b[pid], 0, 1))

# Ordering variables and non-overlap with travel times
y = {}  # directional order vars
for i in range(len(people)):
    for j in range(len(people)):
        if i == j:
            continue
        ni = people[i]["name"]
        nj = people[j]["name"]
        y[(ni, nj)] = Bool(f"y_{ni}_before_{nj}")

# For each unordered pair, enforce XOR order if both are met, and link travel-time non-overlap
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        loc_i = pi["location"]
        loc_j = pj["location"]
        tij = travel[loc_i][loc_j]
        tji = travel[loc_j][loc_i]

        # If both are met, exactly one ordering must hold; if either not met, both y's are false
        opt.add(Implies(And(b[ni], b[nj]), Xor(y[(ni, nj)], y[(nj, ni)])))
        opt.add(Implies(y[(ni, nj)], And(b[ni], b[nj])))
        opt.add(Implies(y[(nj, ni)], And(b[ni], b[nj])))

        # Non-overlap + travel time depending on direction
        opt.add(s[nj] >= s[ni] + d[ni] + tij - M_big * If(y[(ni, nj)], 0, 1))
        opt.add(s[ni] >= s[nj] + d[nj] + tji - M_big * If(y[(nj, ni)], 0, 1))

# Objectives: maximize number met, then maximize total meeting time
total_met = Sum([If(b[p["name"]], 1, 0) for p in people])
total_duration = Sum([d[p["name"]] for p in people])

# Ensure at least one meeting (safety)
opt.add(total_met >= 1)

opt.maximize(total_met)
opt.maximize(total_duration)

# Solve
res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit

model = opt.model()

# Extract itinerary
itinerary = []
for p in people:
    pid = p["name"]
    meet_flag = is_true(model.evaluate(b[pid], model_completion=True))
    if meet_flag:
        start_val = model.evaluate(s[pid], model_completion=True).as_long()
        dur_val = model.evaluate(d[pid], model_completion=True).as_long()
        if dur_val > 0:
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": pid,
                "start_minutes": start_val,
                "end_minutes": start_val + dur_val,
                "start_time": minutes_to_str24(start_val),
                "end_time": minutes_to_str24(start_val + dur_val)
            })

# Sort by start time
itinerary.sort(key=lambda x: x["start_minutes"])

# Output without the helper minute fields if you prefer a leaner JSON
lean_itinerary = [{
    "action": e["action"],
    "location": e["location"],
    "person": e["person"],
    "start_time": e["start_time"],
    "end_time": e["end_time"]
} for e in itinerary]

print(json.dumps({"itinerary": lean_itinerary}, ensure_ascii=False))