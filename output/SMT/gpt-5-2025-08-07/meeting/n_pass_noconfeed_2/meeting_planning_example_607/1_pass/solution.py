# SOLUTION:
from z3 import Optimize, Int, Bool, And, Or, Not, If, Sum, is_true
import json

# Time helpers
def mins(h, m):
    return h * 60 + m

def time_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Locations
Sunset = "Sunset District"
RussianHill = "Russian Hill"
TheCastro = "The Castro"
Richmond = "Richmond District"
Marina = "Marina District"
NorthBeach = "North Beach"
UnionSquare = "Union Square"
GoldenGatePark = "Golden Gate Park"

locations = [Sunset, RussianHill, TheCastro, Richmond, Marina, NorthBeach, UnionSquare, GoldenGatePark]

# Directed travel times (minutes)
travel = {}

def set_travel(a, b, t):
    travel[(a, b)] = t

# Sunset District
set_travel(Sunset, RussianHill, 24)
set_travel(Sunset, TheCastro, 17)
set_travel(Sunset, Richmond, 12)
set_travel(Sunset, Marina, 21)
set_travel(Sunset, NorthBeach, 29)
set_travel(Sunset, UnionSquare, 30)
set_travel(Sunset, GoldenGatePark, 11)

# Russian Hill
set_travel(RussianHill, Sunset, 23)
set_travel(RussianHill, TheCastro, 21)
set_travel(RussianHill, Richmond, 14)
set_travel(RussianHill, Marina, 7)
set_travel(RussianHill, NorthBeach, 5)
set_travel(RussianHill, UnionSquare, 11)
set_travel(RussianHill, GoldenGatePark, 21)

# The Castro
set_travel(TheCastro, Sunset, 17)
set_travel(TheCastro, RussianHill, 18)
set_travel(TheCastro, Richmond, 16)
set_travel(TheCastro, Marina, 21)
set_travel(TheCastro, NorthBeach, 20)
set_travel(TheCastro, UnionSquare, 19)
set_travel(TheCastro, GoldenGatePark, 11)

# Richmond District
set_travel(Richmond, Sunset, 11)
set_travel(Richmond, RussianHill, 13)
set_travel(Richmond, TheCastro, 16)
set_travel(Richmond, Marina, 9)
set_travel(Richmond, NorthBeach, 17)
set_travel(Richmond, UnionSquare, 21)
set_travel(Richmond, GoldenGatePark, 9)

# Marina District
set_travel(Marina, Sunset, 19)
set_travel(Marina, RussianHill, 8)
set_travel(Marina, TheCastro, 22)
set_travel(Marina, Richmond, 11)
set_travel(Marina, NorthBeach, 11)
set_travel(Marina, UnionSquare, 16)
set_travel(Marina, GoldenGatePark, 18)

# North Beach
set_travel(NorthBeach, Sunset, 27)
set_travel(NorthBeach, RussianHill, 4)
set_travel(NorthBeach, TheCastro, 22)
set_travel(NorthBeach, Richmond, 18)
set_travel(NorthBeach, Marina, 9)
set_travel(NorthBeach, UnionSquare, 7)
set_travel(NorthBeach, GoldenGatePark, 22)

# Union Square
set_travel(UnionSquare, Sunset, 26)
set_travel(UnionSquare, RussianHill, 13)
set_travel(UnionSquare, TheCastro, 19)
set_travel(UnionSquare, Richmond, 20)
set_travel(UnionSquare, Marina, 18)
set_travel(UnionSquare, NorthBeach, 10)
set_travel(UnionSquare, GoldenGatePark, 22)

# Golden Gate Park
set_travel(GoldenGatePark, Sunset, 10)
set_travel(GoldenGatePark, RussianHill, 19)
set_travel(GoldenGatePark, TheCastro, 13)
set_travel(GoldenGatePark, Richmond, 7)
set_travel(GoldenGatePark, Marina, 16)
set_travel(GoldenGatePark, NorthBeach, 24)
set_travel(GoldenGatePark, UnionSquare, 22)

# Self-travel is zero
for a in locations:
    set_travel(a, a, 0)

# Day parameters
start_location = Sunset
day_start = mins(9, 0)   # 9:00
day_end = mins(22, 0)    # 22:00

# Friends data
friends = [
    {
        "name": "Karen",
        "location": RussianHill,
        "avail_start": mins(20, 45),  # 8:45PM
        "avail_end": mins(21, 45),    # 9:45PM
        "min_dur": 60
    },
    {
        "name": "Jessica",
        "location": TheCastro,
        "avail_start": mins(15, 45),  # 3:45PM
        "avail_end": mins(19, 30),    # 7:30PM
        "min_dur": 60
    },
    {
        "name": "Matthew",
        "location": Richmond,
        "avail_start": mins(7, 30),   # 7:30AM
        "avail_end": mins(15, 15),    # 3:15PM
        "min_dur": 15
    },
    {
        "name": "Michelle",
        "location": Marina,
        "avail_start": mins(10, 30),  # 10:30AM
        "avail_end": mins(18, 45),    # 6:45PM
        "min_dur": 75
    },
    {
        "name": "Carol",
        "location": NorthBeach,
        "avail_start": mins(12, 0),   # 12:00PM
        "avail_end": mins(17, 0),     # 5:00PM
        "min_dur": 90
    },
    {
        "name": "Stephanie",
        "location": UnionSquare,
        "avail_start": mins(10, 45),  # 10:45AM
        "avail_end": mins(14, 15),    # 2:15PM
        "min_dur": 30
    },
    {
        "name": "Linda",
        "location": GoldenGatePark,
        "avail_start": mins(10, 45),  # 10:45AM
        "avail_end": mins(22, 0),     # 10:00PM
        "min_dur": 90
    },
]

# Build solver
opt = Optimize()

# Variables
vars_map = {}  # name -> dict with z3 vars
for f in friends:
    pname = f["name"]
    s = Int(f"s_{pname}")
    e = Int(f"e_{pname}")
    meet = Bool(f"meet_{pname}")
    vars_map[pname] = {"s": s, "e": e, "meet": meet, "location": f["location"]}

    # General bounds
    opt.add(s >= 0, e >= 0, e <= 24 * 60)

    # If meeting, enforce availability, min duration, and start travel feasibility
    opt.add(Implies(
        meet,
        And(
            s >= f["avail_start"],
            e <= f["avail_end"],
            s >= day_start + travel[(start_location, f["location"])],
            s >= day_start,  # cannot start before arriving in the city
            e <= day_end,    # end by day end
            e - s >= f["min_dur"]
        )
    ))

    # If not meeting, collapse interval to zero (helps solver)
    opt.add(Implies(Not(meet), And(s == 0, e == 0)))

# Pairwise non-overlap with travel time
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        pi = vars_map[fi["name"]]
        pj = vars_map[fj["name"]]
        t_ij = travel[(fi["location"], fj["location"])]
        t_ji = travel[(fj["location"], fi["location"])]
        # If both meetings occur, either i precedes j with travel or j precedes i with travel
        opt.add(Or(
            Not(pi["meet"]),
            Not(pj["meet"]),
            pi["e"] + t_ij <= pj["s"],
            pj["e"] + t_ji <= pi["s"]
        ))

# Objective: maximize number of meetings, then maximize total meeting minutes
total_meetings = Sum([If(vars_map[f["name"]]["meet"], 1, 0) for f in friends])
total_minutes = Sum([If(vars_map[f["name"]]["meet"], vars_map[f["name"]]["e"] - vars_map[f["name"]]["s"], 0) for f in friends])
opt.maximize(total_meetings)
opt.maximize(total_minutes)

# Solve
if opt.check() != 1:  # unsat
    result = {"itinerary": []}
else:
    model = opt.model()
    itinerary = []
    for f in friends:
        v = vars_map[f["name"]]
        if is_true(model.evaluate(v["meet"])):
            s_val = model.evaluate(v["s"]).as_long()
            e_val = model.evaluate(v["e"]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": time_str(s_val),
                "end_time": time_str(e_val)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    result = {"itinerary": itinerary}

print(json.dumps(result, ensure_ascii=False))