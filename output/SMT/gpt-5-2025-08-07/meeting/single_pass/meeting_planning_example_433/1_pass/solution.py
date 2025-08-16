from z3 import Optimize, Int, Bool, If, Or, And, Implies, Sum
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem data
arrival_location = "Nob Hill"
arrival_time = to_minutes("09:00")

friends = [
    {
        "name": "Emily",
        "location": "Richmond District",
        "window_start": to_minutes("19:00"),
        "window_end": to_minutes("21:00"),
        "min_duration": 15,
    },
    {
        "name": "Margaret",
        "location": "Financial District",
        "window_start": to_minutes("16:30"),
        "window_end": to_minutes("20:15"),
        "min_duration": 75,
    },
    {
        "name": "Ronald",
        "location": "North Beach",
        "window_start": to_minutes("18:30"),
        "window_end": to_minutes("19:30"),
        "min_duration": 45,
    },
    {
        "name": "Deborah",
        "location": "The Castro",
        "window_start": to_minutes("13:45"),
        "window_end": to_minutes("21:15"),
        "min_duration": 90,
    },
    {
        "name": "Jeffrey",
        "location": "Golden Gate Park",
        "window_start": to_minutes("11:15"),
        "window_end": to_minutes("14:30"),
        "min_duration": 120,
    },
]

# Directed travel times in minutes
travel_times = {
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,

    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,

    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,

    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,

    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

def ttime(a, b):
    return travel_times[(a, b)]

# Build solver
opt = Optimize()

n = len(friends)
start_vars = []
end_vars = []
meet_vars = []

for i, f in enumerate(friends):
    s = Int(f"s_{i}")
    e = Int(f"e_{i}")
    m = Bool(f"meet_{i}")
    start_vars.append(s)
    end_vars.append(e)
    meet_vars.append(m)

    # Meeting within window, respecting duration
    opt.add(Implies(m, s >= f["window_start"]))
    opt.add(Implies(m, e <= f["window_end"]))
    opt.add(Implies(m, e - s >= f["min_duration"]))

    # Feasible times (basic bounds)
    opt.add(Implies(m, s >= 0))
    opt.add(Implies(m, e >= 0))

    # You must be able to get to that location from arrival by start time
    opt.add(Implies(m, s >= arrival_time + ttime(arrival_location, f["location"])))

# Non-overlap with travel time between any two met friends; introduce ordering booleans
before = {}
for i in range(n):
    for j in range(i + 1, n):
        b = Bool(f"before_{i}_{j}")
        before[(i, j)] = b

        # If both are met, enforce that either i before j or j before i with travel time
        ti = friends[i]["location"]
        tj = friends[j]["location"]

        opt.add(Implies(And(meet_vars[i], meet_vars[j], b),
                        end_vars[i] + ttime(ti, tj) <= start_vars[j]))
        opt.add(Implies(And(meet_vars[i], meet_vars[j], Not(b)),
                        end_vars[j] + ttime(tj, ti) <= start_vars[i]))

# Objective: maximize number of people met
total_met = Sum([If(m, 1, 0) for m in meet_vars])
opt.maximize(total_met)

# Secondary objective: minimize sum of end times to bias towards earlier finish times
opt.minimize(Sum([If(meet_vars[i], end_vars[i], 0) for i in range(n)]))

# Solve
res = opt.check()
if str(res) != "sat":
    # If somehow unsat, return empty itinerary
    print(json.dumps({"itinerary": []}))
    raise SystemExit

model = opt.model()

# Extract meetings
meetings = []
for i, f in enumerate(friends):
    if model.eval(meet_vars[i], model_completion=True):
        s = model.eval(start_vars[i]).as_long()
        e = model.eval(end_vars[i]).as_long()
        meetings.append({
            "person": f["name"],
            "start": s,
            "end": e
        })

# Sort by start time
meetings.sort(key=lambda x: x["start"])

# Format output
itinerary = []
for m in meetings:
    itinerary.append({
        "action": "meet",
        "person": m["person"],
        "start_time": to_hhmm(m["start"]),
        "end_time": to_hhmm(m["end"])
    })

print(json.dumps({"itinerary": itinerary}))