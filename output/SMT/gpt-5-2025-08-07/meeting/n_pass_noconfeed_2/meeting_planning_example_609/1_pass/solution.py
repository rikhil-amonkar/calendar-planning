import json
from z3 import Optimize, Int, IntVal, If, And, Or, Implies

def minutes(h, m):
    return h * 60 + m

def time_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# People and their constraints
people = [
    {"name": "David",   "location": "Mission District",   "avail_start": minutes(8,0),  "avail_end": minutes(19,45), "min_dur": 45},
    {"name": "Kenneth", "location": "Alamo Square",       "avail_start": minutes(14,0), "avail_end": minutes(19,45), "min_dur": 120},
    {"name": "John",    "location": "Pacific Heights",    "avail_start": minutes(17,0), "avail_end": minutes(20,0),  "min_dur": 15},
    {"name": "Charles", "location": "Union Square",       "avail_start": minutes(21,45),"avail_end": minutes(22,45), "min_dur": 60},
    {"name": "Deborah", "location": "Golden Gate Park",   "avail_start": minutes(7,0),  "avail_end": minutes(18,15), "min_dur": 90},
    {"name": "Karen",   "location": "Sunset District",    "avail_start": minutes(17,45),"avail_end": minutes(21,15), "min_dur": 15},
    {"name": "Carol",   "location": "Presidio",           "avail_start": minutes(8,15), "avail_end": minutes(9,15),  "min_dur": 30},
]

locations = [p["location"] for p in people]
names = [p["name"] for p in people]
avail_starts = [p["avail_start"] for p in people]
avail_ends   = [p["avail_end"] for p in people]
min_durs     = [p["min_dur"] for p in people]

# Travel times between friends' locations (minutes), indices correspond to "locations"
# Index mapping:
# 0 Mission District, 1 Alamo Square, 2 Pacific Heights, 3 Union Square,
# 4 Golden Gate Park, 5 Sunset District, 6 Presidio
N = len(people)

travel = [
    # From Mission District
    [0, 11, 16, 15, 17, 24, 25],
    # From Alamo Square
    [10, 0, 10, 14, 9, 16, 18],
    # From Pacific Heights
    [15, 10, 0, 12, 15, 21, 11],
    # From Union Square
    [14, 15, 15, 0, 22, 26, 24],
    # From Golden Gate Park
    [17, 10, 16, 22, 0, 10, 11],
    # From Sunset District
    [24, 17, 21, 30, 11, 0, 16],
    # From Presidio
    [26, 18, 11, 22, 12, 15, 0],
]

# Travel from Chinatown (start) to each location
chinatown_to = [
    18, # to Mission District
    17, # to Alamo Square
    10, # to Pacific Heights
    7,  # to Union Square
    23, # to Golden Gate Park
    29, # to Sunset District
    19, # to Presidio
]

start_city = "Chinatown"
start_time = minutes(9,0)  # 9:00

# Helper to build piecewise expression selecting value by index variable
def piecewise_from_index(idx, values):
    # values: list of ints
    expr = IntVal(values[-1])
    for i in range(len(values)-2, -1, -1):
        expr = If(idx == i, IntVal(values[i]), expr)
    return expr

def travel_expr(i_idx, j_idx):
    # Returns z3 expression for travel[i_idx][j_idx]
    # Build nested Ifs
    row_expr = piecewise_from_index(j_idx, travel[-1])
    for i in range(N-2, -1, -1):
        row_expr = If(i_idx == i, piecewise_from_index(j_idx, travel[i]), row_expr)
    return row_expr

# Build SMT model
opt = Optimize()

used_count = Int("used_count")
opt.add(used_count >= 0, used_count <= N)

assign = [Int(f"assign_{k}") for k in range(N)]
start_vars = [Int(f"start_{k}") for k in range(N)]
end_vars = [Int(f"end_{k}") for k in range(N)]

for k in range(N):
    opt.add(assign[k] >= 0, assign[k] < N)
    opt.add(start_vars[k] >= 0, start_vars[k] <= 24*60)
    opt.add(end_vars[k] >= 0, end_vars[k] <= 24*60)
    # If slot is unused (k >= used_count), collapse its interval
    opt.add(Implies(Not(k < used_count), end_vars[k] == start_vars[k]))

# Each used slot must satisfy meeting constraints for the assigned person
for k in range(N):
    p_start = piecewise_from_index(assign[k], avail_starts)
    p_end   = piecewise_from_index(assign[k], avail_ends)
    p_min   = piecewise_from_index(assign[k], min_durs)
    opt.add(Implies(k < used_count, And(
        start_vars[k] >= p_start,
        end_vars[k]   <= p_end,
        end_vars[k] - start_vars[k] >= p_min
    )))

# All assigned persons in used slots must be distinct
for i in range(N):
    for j in range(i+1, N):
        opt.add(Implies(And(i < used_count, j < used_count), assign[i] != assign[j]))

# Travel feasibility between consecutive used slots
for k in range(N-1):
    t_expr = travel_expr(assign[k], assign[k+1])
    opt.add(Implies((k + 1) < used_count, start_vars[k+1] >= end_vars[k] + t_expr))

# First meeting reachable from Chinatown at 9:00
first_leg = piecewise_from_index(assign[0], chinatown_to)
opt.add(Implies(used_count > 0, start_vars[0] >= IntVal(start_time) + first_leg))

# Objective: maximize number of meetings
opt.maximize(used_count)

# Tie-breaker: minimize the end time of the last meeting
# Build piecewise last_end based on used_count
last_end = IntVal(start_time)
for t in range(1, N+1):
    last_end = If(used_count == t, end_vars[t-1], last_end)
opt.minimize(last_end)

# Solve
if opt.check() != None:
    model = opt.model()
    count = model.eval(used_count).as_long()

    itinerary = []
    for k in range(count):
        p_idx = model.eval(assign[k]).as_long()
        st = model.eval(start_vars[k]).as_long()
        en = model.eval(end_vars[k]).as_long()
        itinerary.append({
            "action": "meet",
            "location": locations[p_idx],
            "person": names[p_idx],
            "start_time": time_to_str(st),
            "end_time": time_to_str(en)
        })

    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False))