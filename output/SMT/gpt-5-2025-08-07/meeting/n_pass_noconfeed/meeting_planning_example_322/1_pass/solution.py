import json
from z3 import Optimize, Int, Bool, And, Or, If, Implies, Not, Sum

# Helper functions
def hm(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
locations = [
    "Sunset District",
    "Russian Hill",
    "Chinatown",
    "Presidio",
    "Fisherman's Wharf"
]

T = {loc: {} for loc in locations}
# Sunset District to others
T["Sunset District"]["Russian Hill"] = 24
T["Sunset District"]["Chinatown"] = 30
T["Sunset District"]["Presidio"] = 16
T["Sunset District"]["Fisherman's Wharf"] = 29
# Russian Hill to others
T["Russian Hill"]["Sunset District"] = 23
T["Russian Hill"]["Chinatown"] = 9
T["Russian Hill"]["Presidio"] = 14
T["Russian Hill"]["Fisherman's Wharf"] = 7
# Chinatown to others
T["Chinatown"]["Sunset District"] = 29
T["Chinatown"]["Russian Hill"] = 7
T["Chinatown"]["Presidio"] = 19
T["Chinatown"]["Fisherman's Wharf"] = 8
# Presidio to others
T["Presidio"]["Sunset District"] = 15
T["Presidio"]["Russian Hill"] = 14
T["Presidio"]["Chinatown"] = 21
T["Presidio"]["Fisherman's Wharf"] = 19
# Fisherman's Wharf to others
T["Fisherman's Wharf"]["Sunset District"] = 27
T["Fisherman's Wharf"]["Russian Hill"] = 7
T["Fisherman's Wharf"]["Chinatown"] = 12
T["Fisherman's Wharf"]["Presidio"] = 17

# People and their constraints
people = [
    {
        "name": "William",
        "location": "Russian Hill",
        "window_start": hm(18, 30),  # 6:30 PM
        "window_end": hm(20, 45),    # 8:45 PM
        "min_meet": 105
    },
    {
        "name": "Michelle",
        "location": "Chinatown",
        "window_start": hm(8, 15),
        "window_end": hm(14, 0),
        "min_meet": 15
    },
    {
        "name": "George",
        "location": "Presidio",
        "window_start": hm(10, 30),
        "window_end": hm(18, 45),
        "min_meet": 30
    },
    {
        "name": "Robert",
        "location": "Fisherman's Wharf",
        "window_start": hm(9, 0),
        "window_end": hm(13, 45),
        "min_meet": 30
    }
]

# Day start: arrive at Sunset District at 9:00 AM
start_location = "Sunset District"
arrival_time = hm(9, 0)

n = len(people)

opt = Optimize()
opt.set(priority='lex')

# Decision variables
S = [Int(f"s_{i}") for i in range(n)]       # start times (minutes after midnight)
D = [Int(f"d_{i}") for i in range(n)]       # durations (minutes)
Met = [Bool(f"met_{i}") for i in range(n)]  # whether we meet this person

# Pairwise ordering variables
Order = {}
for i in range(n):
    for j in range(i + 1, n):
        Order[(i, j)] = Bool(f"order_{i}_{j}")  # True => i before j, False => j before i

# Constraints
DAY_END = 24 * 60

for i, p in enumerate(people):
    # Bounds on variables
    opt.add(S[i] >= 0, S[i] <= DAY_END)
    opt.add(D[i] >= 0, D[i] <= DAY_END)

    # If met, must meet within availability window and satisfy minimum duration
    opt.add(Implies(Met[i], And(
        S[i] >= p["window_start"],
        S[i] + D[i] <= p["window_end"],
        D[i] >= p["min_meet"]
    )))

    # If not met, duration is zero
    opt.add(Implies(Not(Met[i]), D[i] == 0))

    # Cannot start earlier than possible from arrival via direct travel from Sunset
    travel_from_start = T[start_location][p["location"]]
    opt.add(Implies(Met[i], S[i] >= arrival_time + travel_from_start))

# Travel-time-aware non-overlap/order between meetings
for i in range(n):
    for j in range(i + 1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        tij = T[li][lj]
        tji = T[lj][li]
        oij = Order[(i, j)]
        # If both met and i before j, then j must start after i ends plus travel time
        opt.add(Implies(And(Met[i], Met[j], oij), S[j] >= S[i] + D[i] + tij))
        # If both met and j before i, then i must start after j ends plus travel time
        opt.add(Implies(And(Met[i], Met[j], Not(oij)), S[i] >= S[j] + D[j] + tji))

# Objectives:
# 1) Maximize number of friends met
opt.maximize(Sum([If(Met[i], 1, 0) for i in range(n)]))
# 2) Maximize total meeting time as a tie-breaker
opt.maximize(Sum([D[i] for i in range(n)]))

# Solve
result = opt.check()
itinerary = []

if str(result) == "sat":
    m = opt.model()
    meetings = []
    for i, p in enumerate(people):
        met_val = m.evaluate(Met[i])
        if str(met_val) == "True":
            s_val = m.evaluate(S[i]).as_long()
            d_val = m.evaluate(D[i]).as_long()
            e_val = s_val + d_val
            meetings.append({
                "person": p["name"],
                "location": p["location"],
                "start": s_val,
                "end": e_val
            })
    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start"])
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": fmt(mt["start"]),
            "end_time": fmt(mt["end"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))