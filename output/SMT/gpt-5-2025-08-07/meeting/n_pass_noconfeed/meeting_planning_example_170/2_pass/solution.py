import json
from z3 import Int, Bool, Optimize, And, Or, Implies, If, sat, is_true

def minutes_to_str(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

def solve():
    # Locations
    NB = "North Beach"
    US = "Union Square"
    RH = "Russian Hill"

    # Travel times (minutes), asymmetric
    travel = {
        (NB, US): 7,
        (NB, RH): 4,
        (US, NB): 10,
        (US, RH): 13,
        (RH, NB): 5,
        (RH, US): 11,
    }

    # Start info
    start_loc = NB
    start_time = 9 * 60  # 9:00

    # People constraints
    Emily = {
        "name": "Emily",
        "location": US,
        "avail_start": 16 * 60,           # 16:00
        "avail_end": 17 * 60 + 15,        # 17:15
        "min_dur": 45
    }
    Margaret = {
        "name": "Margaret",
        "location": RH,
        "avail_start": 19 * 60,           # 19:00
        "avail_end": 21 * 60,             # 21:00
        "min_dur": 120
    }

    # Z3 variables
    E_meet = Bool("E_meet")
    E_start = Int("E_start")
    E_end = Int("E_end")

    M_meet = Bool("M_meet")
    M_start = Int("M_start")
    M_end = Int("M_end")

    opt = Optimize()
    opt.set("priority", "lex")

    DAY_MIN = 0
    DAY_MAX = 24 * 60

    # Domain bounds
    for v in [E_start, E_end, M_start, M_end]:
        opt.add(v >= DAY_MIN, v <= DAY_MAX)

    # Meeting window and duration constraints
    # Emily
    opt.add(Implies(E_meet, And(
        E_start >= Emily["avail_start"],
        E_end <= Emily["avail_end"],
        E_end > E_start,
        E_end - E_start >= Emily["min_dur"]
    )))
    # If not meeting, keep a sane relation to avoid unconstrained weirdness
    opt.add(Implies(~E_meet, And(
        E_start == Emily["avail_start"],
        E_end == Emily["avail_start"]
    )))

    # Margaret
    opt.add(Implies(M_meet, And(
        M_start >= Margaret["avail_start"],
        M_end <= Margaret["avail_end"],
        M_end > M_start,
        M_end - M_start >= Margaret["min_dur"]
    )))
    opt.add(Implies(~M_meet, And(
        M_start == Margaret["avail_start"],
        M_end == Margaret["avail_start"]
    )))

    # Travel feasibility constraints
    # Single meeting cases: reachable from start location
    opt.add(Implies(And(E_meet, ~M_meet), E_start >= start_time + travel[(start_loc, Emily["location"])]))
    opt.add(Implies(And(M_meet, ~E_meet), M_start >= start_time + travel[(start_loc, Margaret["location"])]))

    # Both meetings case: enforce a feasible order and travel
    cond_E_then_M = And(
        E_end + travel[(Emily["location"], Margaret["location"])] <= M_start,
        E_start >= start_time + travel[(start_loc, Emily["location"])]
    )
    cond_M_then_E = And(
        M_end + travel[(Margaret["location"], Emily["location"])] <= E_start,
        M_start >= start_time + travel[(start_loc, Margaret["location"])]
    )
    opt.add(Implies(And(E_meet, M_meet), Or(cond_E_then_M, cond_M_then_E)))

    # Objective 1: maximize number of friends met
    opt.maximize(If(E_meet, 1, 0) + If(M_meet, 1, 0))

    # Objective 2: maximize total meeting duration
    total_duration = If(E_meet, E_end - E_start, 0) + If(M_meet, M_end - M_start, 0)
    opt.maximize(total_duration)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    itinerary = []

    if is_true(model.evaluate(E_meet)):
        itinerary.append({
            "action": "meet",
            "location": Emily["location"],
            "person": Emily["name"],
            "start_time": minutes_to_str(model.evaluate(E_start).as_long()),
            "end_time": minutes_to_str(model.evaluate(E_end).as_long())
        })

    if is_true(model.evaluate(M_meet)):
        itinerary.append({
            "action": "meet",
            "location": Margaret["location"],
            "person": Margaret["name"],
            "start_time": minutes_to_str(model.evaluate(M_start).as_long()),
            "end_time": minutes_to_str(model.evaluate(M_end).as_long())
        })

    # Sort itinerary chronologically
    def time_to_minutes(tstr):
        h, m = map(int, tstr.split(":"))
        return h * 60 + m

    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve()