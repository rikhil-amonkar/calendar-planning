import json
import sys
import subprocess

# Ensure z3 is available
try:
    from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, is_true
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "z3-solver", "-q"])
    from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, is_true

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def compute_schedule():
    # Input parameters
    locations = ["North Beach", "Union Square", "Russian Hill"]
    travel = {
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11
    }
    start_location = "North Beach"
    start_time = 9 * 60  # 9:00 -> 540 minutes

    # Friends constraints
    # Emily @ Union Square: 16:00 - 17:15, min 45
    emily = {
        "name": "Emily",
        "location": "Union Square",
        "window_start": 16*60,    # 960
        "window_end": 17*60 + 15, # 1035
        "min_duration": 45
    }
    # Margaret @ Russian Hill: 19:00 - 21:00, min 120
    margaret = {
        "name": "Margaret",
        "location": "Russian Hill",
        "window_start": 19*60,    # 1140
        "window_end": 21*60,      # 1260
        "min_duration": 120
    }

    # Z3 variables
    opt = Optimize()

    eStart, eEnd = Int('eStart'), Int('eEnd')
    mStart, mEnd = Int('mStart'), Int('mEnd')

    eMeet = Bool('eMeet')
    mMeet = Bool('mMeet')

    # Order boolean: True if Emily before Margaret when both are met
    ord_e_first = Bool('ord_e_first')

    # Bounds on times (0..1440)
    for v in [eStart, eEnd, mStart, mEnd]:
        opt.add(v >= 0, v <= 24*60)

    # Meeting window and duration constraints
    opt.add(Implies(eMeet, And(
        eStart >= emily["window_start"],
        eEnd <= emily["window_end"],
        eEnd - eStart >= emily["min_duration"]
    )))
    opt.add(Implies(Not(eMeet), eEnd == eStart))  # collapse times if not meeting

    opt.add(Implies(mMeet, And(
        mStart >= margaret["window_start"],
        mEnd <= margaret["window_end"],
        mEnd - mStart >= margaret["min_duration"]
    )))
    opt.add(Implies(Not(mMeet), mEnd == mStart))  # collapse times if not meeting

    # Travel constraints
    t_nb_us = travel[(start_location, "Union Square")]
    t_nb_rh = travel[(start_location, "Russian Hill")]
    t_us_rh = travel[("Union Square", "Russian Hill")]
    t_rh_us = travel[("Russian Hill", "Union Square")]

    # If meeting only one friend
    opt.add(Implies(And(eMeet, Not(mMeet)), eStart >= start_time + t_nb_us))
    opt.add(Implies(And(mMeet, Not(eMeet)), mStart >= start_time + t_nb_rh))

    # If meeting both, enforce ordering with travel times
    opt.add(Implies(And(eMeet, mMeet, ord_e_first),
                    And(eStart >= start_time + t_nb_us,
                        mStart >= eEnd + t_us_rh)))
    opt.add(Implies(And(eMeet, mMeet, Not(ord_e_first)),
                    And(mStart >= start_time + t_nb_rh,
                        eStart >= mEnd + t_rh_us)))

    # Objective: maximize number of friends met, then total meeting time
    met_count = If(eMeet, 1, 0) + If(mMeet, 1, 0)
    total_duration = If(eMeet, eEnd - eStart, 0) + If(mMeet, mEnd - mStart, 0)

    opt.maximize(met_count)
    opt.maximize(total_duration)

    # Solve
    if opt.check() != 1:  # sat
        return {"itinerary": []}

    model = opt.model()

    itinerary = []
    if is_true(model[eMeet]):
        itinerary.append({
            "action": "meet",
            "location": emily["location"],
            "person": emily["name"],
            "start_time": minutes_to_time(model[eStart].as_long()),
            "end_time": minutes_to_time(model[eEnd].as_long())
        })
    if is_true(model[mMeet]):
        itinerary.append({
            "action": "meet",
            "location": margaret["location"],
            "person": margaret["name"],
            "start_time": minutes_to_time(model[mStart].as_long()),
            "end_time": minutes_to_time(model[mEnd].as_long())
        })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_schedule()
    print(json.dumps(result, ensure_ascii=False))