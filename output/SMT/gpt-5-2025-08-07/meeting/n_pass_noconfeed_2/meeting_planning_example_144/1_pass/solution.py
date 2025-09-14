import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Input parameters (as variables)
    locations = ["The Castro", "Mission District", "Financial District"]

    # Travel times in minutes (asymmetric where specified)
    travel = {
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Financial District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Financial District"): 17,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Mission District"): 17,
    }

    # Arrival info
    arrival_location = "The Castro"
    arrival_time = minutes(9, 0)  # 9:00

    # Friends availability and requirements
    friends = {
        "Laura": {
            "location": "Mission District",
            "start": minutes(12, 15),   # 12:15
            "end": minutes(19, 45),     # 19:45
            "min_duration": 75
        },
        "Anthony": {
            "location": "Financial District",
            "start": minutes(12, 30),   # 12:30
            "end": minutes(14, 45),     # 14:45
            "min_duration": 30
        }
    }

    # Z3 model
    opt = Optimize()
    opt.set(priority='lex')

    # Variables
    sL, eL = Ints('sL eL')  # Laura meeting start/end
    sA, eA = Ints('sA eA')  # Anthony meeting start/end
    meetL, meetA = Ints('meetL meetA')  # 0/1 decision variables
    ordLA = Int('ordLA')  # 0 => Laura first, 1 => Anthony first

    # Bounds
    DAY_END = 24 * 60
    for v in [sL, eL, sA, eA]:
        opt.add(v >= 0, v <= DAY_END)
    for v in [meetL, meetA, ordLA]:
        opt.add(v >= 0, v <= 1)

    # Helper: availability constraints
    L_avail_start = friends["Laura"]["start"]
    L_avail_end = friends["Laura"]["end"]
    L_min = friends["Laura"]["min_duration"]

    A_avail_start = friends["Anthony"]["start"]
    A_avail_end = friends["Anthony"]["end"]
    A_min = friends["Anthony"]["min_duration"]

    # Meeting active constraints
    opt.add(Implies(meetL == 1, And(sL >= L_avail_start, eL <= L_avail_end, eL - sL >= L_min, eL >= sL)))
    opt.add(Implies(meetA == 1, And(sA >= A_avail_start, eA <= A_avail_end, eA - sA >= A_min, eA >= sA)))

    # If not meeting, force times to 0 to avoid arbitrary values
    opt.add(Implies(meetL == 0, And(sL == 0, eL == 0)))
    opt.add(Implies(meetA == 0, And(sA == 0, eA == 0)))

    # Travel constraints from arrival to first and between meetings
    t_C_M = travel[(arrival_location, "Mission District")]
    t_C_F = travel[(arrival_location, "Financial District")]
    t_M_F = travel[("Mission District", "Financial District")]
    t_F_M = travel[("Financial District", "Mission District")]

    # If only Laura is met
    opt.add(Implies(And(meetL == 1, meetA == 0), sL >= arrival_time + t_C_M))
    # If only Anthony is met
    opt.add(Implies(And(meetA == 1, meetL == 0), sA >= arrival_time + t_C_F))

    # If both are met, enforce an order via ordLA
    opt.add(Implies(And(meetL == 1, meetA == 1, ordLA == 0),
                    And(sL >= arrival_time + t_C_M,  # Start Laura after traveling from Castro
                        sA >= eL + t_M_F)))          # Start Anthony after Laura + travel
    opt.add(Implies(And(meetL == 1, meetA == 1, ordLA == 1),
                    And(sA >= arrival_time + t_C_F,  # Start Anthony after traveling from Castro
                        sL >= eA + t_F_M)))          # Start Laura after Anthony + travel

    # Objective 1: maximize number of friends met
    opt.maximize(meetL + meetA)

    # Objective 2 (tie-breaker): minimize the day finish time (last meeting end)
    last_end_expr = If(And(meetL == 1, meetA == 1), If(eL >= eA, eL, eA),
                       If(meetL == 1, eL, If(meetA == 1, eA, arrival_time)))
    opt.minimize(last_end_expr)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    # Extract results
    mL = model[meetL].as_long()
    mA = model[meetA].as_long()

    itinerary = []

    if mL == 1:
        start = model[sL].as_long()
        end = model[eL].as_long()
        itinerary.append({
            "action": "meet",
            "location": friends["Laura"]["location"],
            "person": "Laura",
            "start_time": fmt_time(start),
            "end_time": fmt_time(end)
        })

    if mA == 1:
        start = model[sA].as_long()
        end = model[eA].as_long()
        itinerary.append({
            "action": "meet",
            "location": friends["Anthony"]["location"],
            "person": "Anthony",
            "start_time": fmt_time(start),
            "end_time": fmt_time(end)
        })

    # Sort itinerary by start_time (numeric)
    def to_minutes(tstr):
        h, m = map(int, tstr.split(":"))
        return h * 60 + m

    itinerary.sort(key=lambda x: to_minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()