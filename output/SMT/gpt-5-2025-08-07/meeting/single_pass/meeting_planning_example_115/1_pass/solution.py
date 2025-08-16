# Solve the scheduling problem using Z3 and output a JSON-formatted itinerary.
# We maximize the number of friends met, then maximize total meeting time.
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Sum, sat
import json

def minutes_to_time_str(minutes_from_base, base_hour=9, base_min=0):
    total_minutes = base_hour * 60 + base_min + minutes_from_base
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    # Availability windows (minutes from 09:00)
    # Carol at Marina: 11:30 to 15:00
    C_avail_start = 2 * 60 + 30  # 150
    C_avail_end   = 6 * 60       # 360
    C_min_dur = 60

    # Jessica at Pacific Heights: 15:30 to 16:45
    J_avail_start = 6 * 60 + 30  # 390
    J_avail_end   = 7 * 60 + 45  # 465
    J_min_dur = 45

    # Travel times (minutes)
    t_R_P = 10
    t_R_M = 9
    t_P_R = 12
    t_P_M = 6
    t_M_R = 11
    t_M_P = 7

    # Z3 Model
    opt = Optimize()

    # Variables
    meet_C = Bool("meet_C")
    meet_J = Bool("meet_J")
    orderCJ = Bool("orderCJ")  # If both are met, True => C before J; False => J before C

    start_C = Int("start_C")
    end_C   = Int("end_C")
    start_J = Int("start_J")
    end_J   = Int("end_J")

    # Bounds for times (non-negative)
    opt.add(start_C >= 0, end_C >= 0, start_J >= 0, end_J >= 0)

    # Meeting feasibility constraints
    opt.add(Implies(meet_C, And(start_C >= C_avail_start,
                                end_C <= C_avail_end,
                                end_C - start_C >= C_min_dur)))
    opt.add(Implies(meet_J, And(start_J >= J_avail_start,
                                end_J <= J_avail_end,
                                end_J - start_J >= J_min_dur)))

    both_meet = And(meet_C, meet_J)

    # Travel and ordering constraints
    # If both are met and Carol before Jessica
    opt.add(Implies(And(both_meet, orderCJ),
                    And(
                        # Start from Richmond at 09:00, reach Marina before Carol's meeting
                        start_C >= t_R_M,
                        # Travel from Marina to Pacific before Jessica's meeting
                        start_J >= end_C + t_M_P
                    )))

    # If both are met and Jessica before Carol
    opt.add(Implies(And(both_meet, Not(orderCJ)),
                    And(
                        # Start from Richmond, reach Pacific before Jessica's meeting
                        start_J >= t_R_P,
                        # Travel from Pacific to Marina before Carol's meeting
                        start_C >= end_J + t_P_M
                    )))

    # If only Carol is met
    opt.add(Implies(And(meet_C, Not(meet_J)),
                    start_C >= t_R_M))

    # If only Jessica is met
    opt.add(Implies(And(meet_J, Not(meet_C)),
                    start_J >= t_R_P))

    # Objectives:
    # 1) Maximize number of distinct friends met
    num_meetings = If(meet_C, 1, 0) + If(meet_J, 1, 0)
    opt.maximize(num_meetings)

    # 2) Maximize total meeting duration as tie-breaker
    total_duration = If(meet_C, end_C - start_C, 0) + If(meet_J, end_J - start_J, 0)
    opt.maximize(total_duration)

    # Solve
    result = opt.check()
    itinerary = []

    if result == sat:
        m = opt.model()
        # Collect meetings if scheduled
        entries = []
        if m.evaluate(meet_C, model_completion=True):
            sC = m.evaluate(start_C, model_completion=True).as_long()
            eC = m.evaluate(end_C, model_completion=True).as_long()
            entries.append(("Carol", sC, eC))
        if m.evaluate(meet_J, model_completion=True):
            sJ = m.evaluate(start_J, model_completion=True).as_long()
            eJ = m.evaluate(end_J, model_completion=True).as_long()
            entries.append(("Jessica", sJ, eJ))

        # Sort by start time
        entries.sort(key=lambda x: x[1])

        for person, s, e in entries:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time_str(s),
                "end_time": minutes_to_time_str(e)
            })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()