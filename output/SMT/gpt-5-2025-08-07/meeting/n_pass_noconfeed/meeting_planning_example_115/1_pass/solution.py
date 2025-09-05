import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Parameters
    # Locations
    RICHMOND = "Richmond District"
    PACIFIC = "Pacific Heights"
    MARINA = "Marina District"

    # Travel times (minutes)
    travel_R_to_P = 10
    travel_R_to_M = 9
    travel_P_to_R = 12
    travel_P_to_M = 6
    travel_M_to_R = 11
    travel_M_to_P = 7

    # Arrival
    arrival_time = 9 * 60  # 9:00

    # Friend availability and minimum meeting times
    # Jessica
    jessica_loc = PACIFIC
    jessica_start_window = 15 * 60 + 30  # 15:30
    jessica_end_window = 16 * 60 + 45    # 16:45
    jessica_min = 45

    # Carol
    carol_loc = MARINA
    carol_start_window = 11 * 60 + 30    # 11:30
    carol_end_window = 15 * 60           # 15:00
    carol_min = 60

    # Z3 model
    set_param('opt.priority', 'lex')
    opt = Optimize()

    # Variables
    C_start, C_end = Ints('C_start C_end')
    J_start, J_end = Ints('J_start J_end')
    meetC = Bool('meetC')
    meetJ = Bool('meetJ')
    carol_first = Bool('carol_first')

    # Domains
    for v in [C_start, C_end, J_start, J_end]:
        opt.add(v >= 0, v <= 24 * 60)

    # Meeting feasibility constraints (only enforced if meeting that person)
    opt.add(Implies(meetC, And(
        C_start >= carol_start_window,
        C_end <= carol_end_window,
        C_end - C_start >= carol_min
    )))
    opt.add(Implies(meetJ, And(
        J_start >= jessica_start_window,
        J_end <= jessica_end_window,
        J_end - J_start >= jessica_min
    )))

    # If not meeting, times are zero to keep extraction simple
    opt.add(Implies(Not(meetC), And(C_start == 0, C_end == 0)))
    opt.add(Implies(Not(meetJ), And(J_start == 0, J_end == 0)))

    # Ordering and travel constraints
    both = And(meetC, meetJ)
    onlyC = And(meetC, Not(meetJ))
    onlyJ = And(meetJ, Not(meetC))

    # carol_first only meaningful if both are met
    opt.add(Implies(carol_first, both))

    # If meeting both, enforce order and travel feasibility
    opt.add(Implies(And(both, carol_first), And(
        C_start >= arrival_time + travel_R_to_M,
        J_start >= C_end + travel_M_to_P
    )))
    opt.add(Implies(And(both, Not(carol_first)), And(
        J_start >= arrival_time + travel_R_to_P,
        C_start >= J_end + travel_P_to_M
    )))

    # If meeting only one, ensure arrival + travel feasibility
    opt.add(Implies(onlyC, C_start >= arrival_time + travel_R_to_M))
    opt.add(Implies(onlyJ, J_start >= arrival_time + travel_R_to_P))

    # Objectives
    meet_count = If(meetC, 1, 0) + If(meetJ, 1, 0)
    end_of_day = Max(If(meetC, C_end, 0), If(meetJ, J_end, 0))

    # Waiting time metrics to tighten schedule
    wait_before_first = If(onlyC, C_start - (arrival_time + travel_R_to_M),
                       If(onlyJ, J_start - (arrival_time + travel_R_to_P),
                          If(And(both, carol_first), C_start - (arrival_time + travel_R_to_M),
                             If(And(both, Not(carol_first)), J_start - (arrival_time + travel_R_to_P), 0))))
    wait_between = If(And(both, carol_first), J_start - (C_end + travel_M_to_P),
                  If(And(both, Not(carol_first)), C_start - (J_end + travel_P_to_M),
                     0))
    # Waits are non-negative due to constraints; enforce explicitly for robustness
    opt.add(wait_before_first >= 0, wait_between >= 0)
    total_wait = wait_before_first + wait_between

    # Optimize: maximize meetings, then minimize makespan, then minimize waiting
    opt.maximize(meet_count)
    opt.minimize(end_of_day)
    opt.minimize(total_wait)

    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    meet_c = is_true(model.eval(meetC))
    meet_j = is_true(model.eval(meetJ))

    itinerary = []

    entries = []
    if meet_c:
        cs = model.eval(C_start).as_long()
        ce = model.eval(C_end).as_long()
        entries.append((cs, {
            "action": "meet",
            "location": carol_loc,
            "person": "Carol",
            "start_time": minutes_to_str(cs),
            "end_time": minutes_to_str(ce)
        }))
    if meet_j:
        js = model.eval(J_start).as_long()
        je = model.eval(J_end).as_long()
        entries.append((js, {
            "action": "meet",
            "location": jessica_loc,
            "person": "Jessica",
            "start_time": minutes_to_str(js),
            "end_time": minutes_to_str(je)
        }))

    # Sort by start time
    entries.sort(key=lambda x: x[0])
    itinerary = [e[1] for e in entries]

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()