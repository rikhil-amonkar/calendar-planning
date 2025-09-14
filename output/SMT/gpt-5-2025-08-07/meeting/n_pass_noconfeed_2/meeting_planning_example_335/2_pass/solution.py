import json
from z3 import Int, Bool, If, And, Or, Optimize, Sum, sat, is_true

# Helper functions
def h_m_to_min(h, m):
    return h * 60 + m

def min_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Data setup
locations = [
    "Pacific Heights",
    "North Beach",
    "Financial District",
    "Alamo Square",
    "Mission District"
]

# Travel times in minutes
travel_times = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11,
}

def travel(a, b):
    if a == b:
        return 0
    return travel_times[(a, b)]

# Start at Pacific Heights at 9:00
START_LOCATION = "Pacific Heights"
START_TIME = h_m_to_min(9, 0)

# People and their constraints
people = [
    {"name": "Helen", "location": "North Beach",
     "window_start": h_m_to_min(9, 0), "window_end": h_m_to_min(17, 0), "min_duration": 15},
    {"name": "Betty", "location": "Financial District",
     "window_start": h_m_to_min(19, 0), "window_end": h_m_to_min(21, 45), "min_duration": 90},
    {"name": "Amanda", "location": "Alamo Square",
     "window_start": h_m_to_min(19, 45), "window_end": h_m_to_min(21, 0), "min_duration": 60},
    {"name": "Kevin", "location": "Mission District",
     "window_start": h_m_to_min(10, 45), "window_end": h_m_to_min(14, 45), "min_duration": 45},
]

n = len(people)

# Z3 variables
s = [Int(f"s_{i}") for i in range(n)]          # start times
d = [Int(f"d_{i}") for i in range(n)]          # durations
meet = [Bool(f"meet_{i}") for i in range(n)]   # whether to meet

opt = Optimize()

# Constraints per person
for i, p in enumerate(people):
    ws = p["window_start"]
    we = p["window_end"]
    min_d = p["min_duration"]
    loc = p["location"]

    # Base domains
    opt.add(s[i] >= 0, s[i] <= 24*60)  # within the day
    opt.add(d[i] >= 0, d[i] <= (we - ws))  # duration cannot exceed window length

    # If we meet, enforce time window, minimum duration, and start feasibility
    opt.add(If(meet[i],
               And(s[i] >= ws,
                   s[i] + d[i] <= we,
                   d[i] >= min_d,
                   s[i] >= START_TIME + travel(START_LOCATION, loc)),
               d[i] == 0))  # if not meeting, duration = 0

# Pairwise non-overlap and travel feasibility between meetings
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        # If both meetings occur, one must happen before the other with travel time
        opt.add(If(And(meet[i], meet[j]),
                   Or(s[j] >= s[i] + d[i] + travel(li, lj),
                      s[i] >= s[j] + d[j] + travel(lj, li)),
                   True))

# Objective 1: Maximize number of friends met
num_met = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(num_met)

# Objective 2: Minimize end time (makespan) of last meeting
end_eff = [If(meet[i], s[i] + d[i], 0) for i in range(n)]
end_last = Int("end_last")
opt.add(end_last >= 0)
for e in end_eff:
    opt.add(end_last >= e)
opt.minimize(end_last)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()

    # Collect meetings that are scheduled
    events = []
    for i, p in enumerate(people):
        if is_true(m.eval(meet[i])):
            start = m.eval(s[i]).as_long()
            dur = m.eval(d[i]).as_long()
            end = start + dur
            events.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": start,
                "end": end
            })

    # Sort by start time
    events.sort(key=lambda x: x["start"])

    # Format for output
    itinerary = []
    for ev in events:
        itinerary.append({
            "action": "meet",
            "location": ev["location"],
            "person": ev["person"],
            "start_time": min_to_str(ev["start"]),
            "end_time": min_to_str(ev["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))