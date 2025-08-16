# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Sum, sat
import json

def parse_time(s):
    # s is "HH:MM" in 24-hour, but inputs we define programmatically
    h, m = map(int, s.split(":"))
    return h*60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Locations
locs = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park",
]

# Travel times (directed, in minutes) as given
T = {
    "The Castro": {
        "Alamo Square": 8,
        "Richmond District": 16,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 24,
        "Marina District": 21,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
    },
    "Alamo Square": {
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 14,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
    },
    "Richmond District": {
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
    },
    "Financial District": {
        "The Castro": 20,
        "Alamo Square": 17,
        "Richmond District": 21,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Marina District": 15,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
    },
    "Union Square": {
        "The Castro": 17,
        "Alamo Square": 15,
        "Richmond District": 20,
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
    },
    "Fisherman's Wharf": {
        "The Castro": 27,
        "Alamo Square": 21,
        "Richmond District": 18,
        "Financial District": 11,
        "Union Square": 13,
        "Marina District": 9,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
    },
    "Marina District": {
        "The Castro": 22,
        "Alamo Square": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 16,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Alamo Square": 5,
        "Richmond District": 10,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Mission District": 11,
        "Pacific Heights": 12,
        "Golden Gate Park": 7,
    },
    "Mission District": {
        "The Castro": 7,
        "Alamo Square": 11,
        "Richmond District": 20,
        "Financial District": 15,
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Haight-Ashbury": 12,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Alamo Square": 10,
        "Richmond District": 12,
        "Financial District": 13,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Golden Gate Park": 15,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Alamo Square": 9,
        "Richmond District": 7,
        "Financial District": 26,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Pacific Heights": 16,
    },
}

# Friends and constraints
def tm(h, m): return h*60 + m

friends = [
    {"name": "William",  "loc": "Alamo Square",       "win_start": tm(15,15), "win_end": tm(17,15), "min_dur": 60},
    {"name": "Joshua",   "loc": "Richmond District",  "win_start": tm(7,0),   "win_end": tm(20,0),  "min_dur": 15},
    {"name": "Joseph",   "loc": "Financial District", "win_start": tm(11,15), "win_end": tm(13,30), "min_dur": 15},
    {"name": "David",    "loc": "Union Square",       "win_start": tm(16,45), "win_end": tm(19,15), "min_dur": 45},
    {"name": "Brian",    "loc": "Fisherman's Wharf",  "win_start": tm(13,45), "win_end": tm(20,45), "min_dur": 105},
    {"name": "Karen",    "loc": "Marina District",    "win_start": tm(11,30), "win_end": tm(18,30), "min_dur": 15},
    {"name": "Anthony",  "loc": "Haight-Ashbury",     "win_start": tm(7,15),  "win_end": tm(10,30), "min_dur": 30},
    {"name": "Matthew",  "loc": "Mission District",   "win_start": tm(17,15), "win_end": tm(19,15), "min_dur": 120},
    {"name": "Helen",    "loc": "Pacific Heights",    "win_start": tm(8,0),   "win_end": tm(12,0),  "min_dur": 75},
    {"name": "Jeffrey",  "loc": "Golden Gate Park",   "win_start": tm(19,0),  "win_end": tm(21,30), "min_dur": 60},
]

origin = "The Castro"
arrival_time_at_origin = tm(9, 0)

# Build solver
opt = Optimize()
opt.set(priority='lex')  # prioritize objectives in order of addition

n = len(friends)
meet = []
start = []
end = []
dur = []
for i, f in enumerate(friends):
    meet_i = Bool(f"meet_{i}")
    s_i = Int(f"start_{i}")
    e_i = Int(f"end_{i}")
    d_i = Int(f"dur_{i}")
    meet.append(meet_i)
    start.append(s_i)
    end.append(e_i)
    dur.append(d_i)

    ws, we, md = f["win_start"], f["win_end"], f["min_dur"]
    # When meeting: within window and minimum duration
    opt.add(Implies(meet_i, And(s_i >= ws, e_i <= we, d_i >= md, d_i == e_i - s_i)))
    # When not meeting: normalize variables for determinism
    opt.add(Implies(Not(meet_i), And(d_i == 0, s_i == ws, e_i == ws)))
    # Must be reachable from origin considering first departure
    # This is a global lower bound that doesn't hinder later meetings
    opt.add(Implies(meet_i, s_i >= arrival_time_at_origin + T[origin][f["loc"]]))

# Precedence and travel-time constraints between meetings
before = [[None]*n for _ in range(n)]
for i in range(n):
    for j in range(n):
        if i == j: 
            before[i][j] = Bool(f"before_{i}_{j}")
            opt.add(before[i][j] == False)
            continue
        b = Bool(f"before_{i}_{j}")
        before[i][j] = b
        # If i is before j, both must be met
        opt.add(Implies(b, And(meet[i], meet[j])))
        # Travel-time feasibility when i before j
        li, lj = friends[i]["loc"], friends[j]["loc"]
        travel_ij = T[li][lj]
        opt.add(Implies(b, start[j] >= end[i] + travel_ij))

# For any pair where both are met, exactly one order must hold
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(meet[i], meet[j]), Or(before[i][j], before[j][i])))
        # Cannot be both
        opt.add(Not(And(before[i][j], before[j][i])))

# Objective 1: maximize number of friends met
total_met = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(total_met)

# Objective 2: tie-breaker maximize total meeting time
total_meet_minutes = Sum([dur[i] for i in range(n)])
opt.maximize(total_meet_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    # Extract meetings
    schedule = []
    for i, f in enumerate(friends):
        if m.evaluate(meet[i]).is_true():
            s = m.evaluate(start[i]).as_long()
            e = m.evaluate(end[i]).as_long()
            schedule.append({
                "action": "meet",
                "person": f["name"],
                "start_time": fmt_time(s),
                "end_time": fmt_time(e),
                "loc": f["loc"],  # include for internal sort/debug; will strip later
                "s_min": s,
            })
    # Sort by start time
    schedule.sort(key=lambda x: x["s_min"])
    # Strip helper fields
    itinerary = [{"action": x["action"], "person": x["person"], "start_time": x["start_time"], "end_time": x["end_time"]} for x in schedule]
    print(json.dumps({"itinerary": itinerary}))