# Z3-based optimizer for the SF friend-meeting problem
# Maximizes the number of friends met subject to travel times and time windows.

from z3 import Optimize, Int, Bool, If, Sum, And, Or, Not
import json

def parse_hhmm(s):
    hh, mm = map(int, s.split(":"))
    return hh * 60 + mm

def hhmm(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Locations
L = [
    "Marina District",
    "Richmond District",
    "Union Square",
    "Nob Hill",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Embarcadero",
    "Financial District",
    "North Beach",
    "Presidio",
]

# Directed travel time matrix (minutes)
T = {loc: {} for loc in L}
def set_t(frm, to, minutes):
    T[frm][to] = minutes

# Marina District origins
set_t("Marina District", "Richmond District", 11)
set_t("Marina District", "Union Square", 16)
set_t("Marina District", "Nob Hill", 12)
set_t("Marina District", "Fisherman's Wharf", 10)
set_t("Marina District", "Golden Gate Park", 18)
set_t("Marina District", "Embarcadero", 14)
set_t("Marina District", "Financial District", 17)
set_t("Marina District", "North Beach", 11)
set_t("Marina District", "Presidio", 10)

# Richmond District origins
set_t("Richmond District", "Marina District", 9)
set_t("Richmond District", "Union Square", 21)
set_t("Richmond District", "Nob Hill", 17)
set_t("Richmond District", "Fisherman's Wharf", 18)
set_t("Richmond District", "Golden Gate Park", 9)
set_t("Richmond District", "Embarcadero", 19)
set_t("Richmond District", "Financial District", 22)
set_t("Richmond District", "North Beach", 17)
set_t("Richmond District", "Presidio", 7)

# Union Square origins
set_t("Union Square", "Marina District", 18)
set_t("Union Square", "Richmond District", 20)
set_t("Union Square", "Nob Hill", 9)
set_t("Union Square", "Fisherman's Wharf", 15)
set_t("Union Square", "Golden Gate Park", 22)
set_t("Union Square", "Embarcadero", 11)
set_t("Union Square", "Financial District", 9)
set_t("Union Square", "North Beach", 10)
set_t("Union Square", "Presidio", 24)

# Nob Hill origins
set_t("Nob Hill", "Marina District", 11)
set_t("Nob Hill", "Richmond District", 14)
set_t("Nob Hill", "Union Square", 7)
set_t("Nob Hill", "Fisherman's Wharf", 10)
set_t("Nob Hill", "Golden Gate Park", 17)
set_t("Nob Hill", "Embarcadero", 9)
set_t("Nob Hill", "Financial District", 9)
set_t("Nob Hill", "North Beach", 8)
set_t("Nob Hill", "Presidio", 17)

# Fisherman's Wharf origins
set_t("Fisherman's Wharf", "Marina District", 9)
set_t("Fisherman's Wharf", "Richmond District", 18)
set_t("Fisherman's Wharf", "Union Square", 13)
set_t("Fisherman's Wharf", "Nob Hill", 11)
set_t("Fisherman's Wharf", "Golden Gate Park", 25)
set_t("Fisherman's Wharf", "Embarcadero", 8)
set_t("Fisherman's Wharf", "Financial District", 11)
set_t("Fisherman's Wharf", "North Beach", 6)
set_t("Fisherman's Wharf", "Presidio", 17)

# Golden Gate Park origins
set_t("Golden Gate Park", "Marina District", 16)
set_t("Golden Gate Park", "Richmond District", 7)
set_t("Golden Gate Park", "Union Square", 22)
set_t("Golden Gate Park", "Nob Hill", 20)
set_t("Golden Gate Park", "Fisherman's Wharf", 24)
set_t("Golden Gate Park", "Embarcadero", 25)
set_t("Golden Gate Park", "Financial District", 26)
set_t("Golden Gate Park", "North Beach", 23)
set_t("Golden Gate Park", "Presidio", 11)

# Embarcadero origins
set_t("Embarcadero", "Marina District", 12)
set_t("Embarcadero", "Richmond District", 21)
set_t("Embarcadero", "Union Square", 10)
set_t("Embarcadero", "Nob Hill", 10)
set_t("Embarcadero", "Fisherman's Wharf", 6)
set_t("Embarcadero", "Golden Gate Park", 25)
set_t("Embarcadero", "Financial District", 5)
set_t("Embarcadero", "North Beach", 5)
set_t("Embarcadero", "Presidio", 20)

# Financial District origins
set_t("Financial District", "Marina District", 15)
set_t("Financial District", "Richmond District", 21)
set_t("Financial District", "Union Square", 9)
set_t("Financial District", "Nob Hill", 8)
set_t("Financial District", "Fisherman's Wharf", 10)
set_t("Financial District", "Golden Gate Park", 23)
set_t("Financial District", "Embarcadero", 4)
set_t("Financial District", "North Beach", 7)
set_t("Financial District", "Presidio", 22)

# North Beach origins
set_t("North Beach", "Marina District", 9)
set_t("North Beach", "Richmond District", 18)
set_t("North Beach", "Union Square", 7)
set_t("North Beach", "Nob Hill", 7)
set_t("North Beach", "Fisherman's Wharf", 5)
set_t("North Beach", "Golden Gate Park", 22)
set_t("North Beach", "Embarcadero", 6)
set_t("North Beach", "Financial District", 8)
set_t("North Beach", "Presidio", 17)

# Presidio origins
set_t("Presidio", "Marina District", 11)
set_t("Presidio", "Richmond District", 7)
set_t("Presidio", "Union Square", 22)
set_t("Presidio", "Nob Hill", 18)
set_t("Presidio", "Fisherman's Wharf", 19)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Embarcadero", 20)
set_t("Presidio", "Financial District", 23)
set_t("Presidio", "North Beach", 18)

# Friend data (24h)
friends = [
    # name, location, window start, window end, min duration (minutes)
    ("Stephanie", "Richmond District", parse_hhmm("16:15"), parse_hhmm("21:30"), 75),
    ("William", "Union Square", parse_hhmm("10:45"), parse_hhmm("17:30"), 45),
    ("Elizabeth", "Nob Hill", parse_hhmm("12:15"), parse_hhmm("15:00"), 105),
    ("Joseph", "Fisherman's Wharf", parse_hhmm("12:45"), parse_hhmm("14:00"), 75),
    ("Anthony", "Golden Gate Park", parse_hhmm("13:00"), parse_hhmm("20:30"), 75),
    ("Barbara", "Embarcadero", parse_hhmm("19:15"), parse_hhmm("20:30"), 75),
    ("Carol", "Financial District", parse_hhmm("11:45"), parse_hhmm("16:15"), 60),
    ("Sandra", "North Beach", parse_hhmm("10:00"), parse_hhmm("12:30"), 15),
    ("Kenneth", "Presidio", parse_hhmm("21:15"), parse_hhmm("22:15"), 45),
]

# Build nodes: Start (S), each friend, End (E)
S_name = "Start"
E_name = "End"
start_time = parse_hhmm("09:00")
start_loc = "Marina District"

nodes = []
# Start node
nodes.append({
    "name": S_name,
    "loc": start_loc,
    "a": start_time,
    "b": start_time,
    "dur": 0,
    "is_friend": False
})
# Friend nodes
for (nm, loc, a, b, d) in friends:
    nodes.append({
        "name": nm,
        "loc": loc,
        "a": a,
        "b": b,
        "dur": d,
        "is_friend": True
    })
# End node
nodes.append({
    "name": E_name,
    "loc": None,
    "a": 0,
    "b": 24*60 + 300,  # generous
    "dur": 0,
    "is_friend": False
})

N = len(nodes)
S_idx = 0
E_idx = N - 1
friend_indices = [i for i in range(N) if nodes[i]["is_friend"]]

# Travel function between nodes
def travel_time(i, j):
    if i == E_idx or j == S_idx:
        return 0
    if j == E_idx:
        return 0
    if i == S_idx:
        # from start location to first meeting
        return T[start_loc][nodes[j]["loc"]]
    # friend to friend
    return T[nodes[i]["loc"]][nodes[j]["loc"]]

# Z3 variables
opt = Optimize()
opt.set("opt.priority", "lex")

M = 10000

Tvar = [Int(f"T_{i}") for i in range(N)]          # start times
y = [Bool(f"y_{i}") if nodes[i]["is_friend"] else None for i in range(N)]  # selection for friends only

# x[i][j] arc usage
x = [[None for _ in range(N)] for __ in range(N)]
for i in range(N):
    for j in range(N):
        if i == j: 
            continue
        if i == E_idx: 
            continue  # no arcs out of End
        if j == S_idx: 
            continue  # no arcs into Start
        x[i][j] = Bool(f"x_{i}_{j}")

# Start time constraints
# Start node fixed
opt.add(Tvar[S_idx] == start_time)

# Windows for friend nodes
for i in friend_indices:
    a = nodes[i]["a"]
    b = nodes[i]["b"]
    d = nodes[i]["dur"]
    # Only relevant if selected
    # a <= T[i] <= b - d
    opt.add(Tvar[i] >= a - If(y[i], IntVal(0), IntVal(M)))
    opt.add(Tvar[i] <= (b - d) + If(y[i], IntVal(0), IntVal(M)))

# No explicit window for End; it will be constrained by arcs

# Degree constraints
# Start: exactly one outgoing (either to a friend or directly to End)
opt.add(Sum([If(x[S_idx][j], 1, 0) for j in range(N) if x[S_idx][j] is not None]) == 1)

# End: exactly one incoming
opt.add(Sum([If(x[i][E_idx], 1, 0) for i in range(N) if x[i][E_idx] is not None]) == 1)

# For each friend: exactly one predecessor and successor if selected, else zero
for i in friend_indices:
    # outgoing
    out_arcs = [x[i][j] for j in range(N) if x[i][j] is not None]
    in_arcs = [x[j][i] for j in range(N) if x[j][i] is not None]
    opt.add(Sum([If(arc, 1, 0) for arc in out_arcs]) == If(y[i], 1, 0))
    opt.add(Sum([If(arc, 1, 0) for arc in in_arcs]) == If(y[i], 1, 0))

# No arcs into friend i unless i is selected; and arcs from Start/into End must respect selection automatically via degree constraints above

# Time propagation on arcs
for i in range(N):
    for j in range(N):
        if x[i][j] is None:
            continue
        tt = travel_time(i, j)
        di = nodes[i]["dur"]
        # T[j] >= T[i] + dur[i] + tt if arc used
        opt.add(Tvar[j] >= Tvar[i] + di + tt - If(x[i][j], IntVal(0), IntVal(M)))

# Also ensure that if an arc goes into a friend j, j must be selected
for j in friend_indices:
    incoming = [x[i][j] for i in range(N) if x[i][j] is not None]
    for arc in incoming:
        opt.add(Or(Not(arc), y[j]))

# Objective 1: maximize number of friends met
obj1 = Sum([If(y[i], 1, 0) for i in friend_indices])
h1 = opt.maximize(obj1)

# Objective 2: minimize total travel time along used arcs (tie-breaker)
total_travel = []
for i in range(N):
    for j in range(N):
        if x[i][j] is None:
            continue
        total_travel.append(If(x[i][j], travel_time(i, j), 0))
h2 = opt.minimize(Sum(total_travel))

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit

m = opt.model()

# Reconstruct path from Start to End
succ = {}
for i in range(N):
    for j in range(N):
        if x[i][j] is None:
            continue
        if m.evaluate(x[i][j], model_completion=True):
            succ[i] = j

# Follow from Start
itinerary = []
cur = S_idx
while cur in succ:
    nxt = succ[cur]
    if nxt == E_idx:
        break
    if nodes[nxt]["is_friend"]:
        start_m = m.evaluate(Tvar[nxt]).as_long()
        end_m = start_m + nodes[nxt]["dur"]
        itinerary.append({
            "action": "meet",
            "person": nodes[nxt]["name"],
            "start_time": hhmm(start_m),
            "end_time": hhmm(end_m),
        })
    cur = nxt

print(json.dumps({"itinerary": itinerary}, indent=2))