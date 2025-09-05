import json
from z3 import *

def minutes_to_time(m):
    # m is minutes since 9:00
    total = 9*60 + m
    h = total // 60
    mi = total % 60
    return f"{h}:{mi:02d}"

def main():
    # Input parameters
    # Locations
    PH = "Pacific Heights"
    PR = "Presidio"
    MD = "Marina District"

    # Travel times (in minutes)
    travel = {
        (PH, PR): 11,
        (PH, MD): 6,
        (PR, PH): 11,
        (PR, MD): 10,
        (MD, PH): 7,
        (MD, PR): 10,
    }

    # Availability windows (minutes from 9:00)
    # Jason: Presidio 10:00-16:15
    J_start_window = 60
    J_end_window = 435
    J_min_duration = 90

    # Kenneth: Marina District 15:30-16:45
    K_start_window = 390
    K_end_window = 465
    K_min_duration = 45

    # Horizon (minutes from 9:00)
    H = 600

    opt = Optimize()
    opt.set(priority='lex')

    # Decision variables
    meetJ = Int('meetJ')   # 0/1
    meetK = Int('meetK')   # 0/1
    orderJK = Int('orderJK')  # 0 -> K before J, 1 -> J before K

    tJ_start = Int('tJ_start')
    tJ_end = Int('tJ_end')
    tK_start = Int('tK_start')
    tK_end = Int('tK_end')

    dJ = Int('dJ')  # duration Jason
    dK = Int('dK')  # duration Kenneth

    # Domains
    opt.add(And(meetJ >= 0, meetJ <= 1))
    opt.add(And(meetK >= 0, meetK <= 1))
    opt.add(And(orderJK >= 0, orderJK <= 1))

    for v in [tJ_start, tJ_end, tK_start, tK_end]:
        opt.add(And(v >= 0, v <= H))

    opt.add(And(dJ >= 0, dK >= 0))

    # Durations
    opt.add(dJ == If(meetJ == 1, tJ_end - tJ_start, 0))
    opt.add(dK == If(meetK == 1, tK_end - tK_start, 0))

    # If not meeting someone, times are zero
    opt.add(Implies(meetJ == 0, And(tJ_start == 0, tJ_end == 0)))
    opt.add(Implies(meetK == 0, And(tK_start == 0, tK_end == 0)))

    # Availability and minimum duration constraints
    opt.add(Implies(meetJ == 1,
                    And(tJ_start >= J_start_window,
                        tJ_end <= J_end_window,
                        tJ_end > tJ_start,
                        tJ_end - tJ_start >= J_min_duration)))
    opt.add(Implies(meetK == 1,
                    And(tK_start >= K_start_window,
                        tK_end <= K_end_window,
                        tK_end > tK_start,
                        tK_end - tK_start >= K_min_duration)))

    # Travel constraints from initial location (PH at time 0) and between meetings
    # If both meetings:
    #   orderJK == 1: Jason before Kenneth
    opt.add(Implies(And(meetJ == 1, meetK == 1, orderJK == 1),
                    And(
                        tJ_start >= travel[(PH, PR)],
                        tK_start >= tJ_end + travel[(PR, MD)]
                    )))

    #   orderJK == 0: Kenneth before Jason
    opt.add(Implies(And(meetJ == 1, meetK == 1, orderJK == 0),
                    And(
                        tK_start >= travel[(PH, MD)],
                        tJ_start >= tK_end + travel[(MD, PR)]
                    )))

    # If only one meeting, ensure travel from PH to that meeting
    opt.add(Implies(And(meetJ == 1, meetK == 0),
                    tJ_start >= travel[(PH, PR)]))
    opt.add(Implies(And(meetK == 1, meetJ == 0),
                    tK_start >= travel[(PH, MD)]))

    # Optimize:
    # 1) Maximize number of friends met
    meet_count = Int('meet_count')
    opt.add(meet_count == meetJ + meetK)
    opt.maximize(meet_count)

    # 2) Maximize total meeting time
    total_meeting_time = Int('total_meeting_time')
    opt.add(total_meeting_time == dJ + dK)
    opt.maximize(total_meeting_time)

    # Solve
    if opt.check() != sat:
        # Fallback: no feasible plan (unlikely with given data)
        print(json.dumps({"itinerary": []}, indent=2))
        return

    model = opt.model()

    itinerary = []

    if model.eval(meetJ).as_long() == 1:
        js = model.eval(tJ_start).as_long()
        je = model.eval(tJ_end).as_long()
        itinerary.append({
            "action": "meet",
            "location": PR,
            "person": "Jason",
            "start_time": minutes_to_time(js),
            "end_time": minutes_to_time(je)
        })

    if model.eval(meetK).as_long() == 1:
        ks = model.eval(tK_start).as_long()
        ke = model.eval(tK_end).as_long()
        itinerary.append({
            "action": "meet",
            "location": MD,
            "person": "Kenneth",
            "start_time": minutes_to_time(ks),
            "end_time": minutes_to_time(ke)
        })

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()