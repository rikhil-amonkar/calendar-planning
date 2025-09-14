import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Sum, is_true

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations
    PACIFIC_HEIGHTS = "Pacific Heights"
    PRESIDIO = "Presidio"
    MARINA = "Marina District"

    # Travel times (minutes)
    travel = {
        (PACIFIC_HEIGHTS, PRESIDIO): 11,
        (PACIFIC_HEIGHTS, MARINA): 6,
        (PRESIDIO, PACIFIC_HEIGHTS): 11,
        (PRESIDIO, MARINA): 10,
        (MARINA, PACIFIC_HEIGHTS): 7,
        (MARINA, PRESIDIO): 10,
    }

    # Arrival
    arrival_loc = PACIFIC_HEIGHTS
    arrival_time = 9 * 60  # 9:00

    # Friends and availability (minutes from midnight)
    # Jason at Presidio 10:00 - 16:15, min 90
    J_loc = PRESIDIO
    J_start_avail = 10 * 60
    J_end_avail = 16 * 60 + 15
    J_min_dur = 90

    # Kenneth at Marina District 15:30 - 16:45, min 45
    K_loc = MARINA
    K_start_avail = 15 * 60 + 30
    K_end_avail = 16 * 60 + 45
    K_min_dur = 45

    DAY_END = 24 * 60

    # SMT variables
    s = Optimize()
    s.set(priority='lex')

    # Meeting times and selection flags
    J_start = Int("J_start")
    J_end = Int("J_end")
    K_start = Int("K_start")
    K_end = Int("K_end")

    meet_J = Bool("meet_J")
    meet_K = Bool("meet_K")
    J_before_K = Bool("J_before_K")  # relevant only if both meet

    # Domains
    s.add(J_start >= 0, J_start <= DAY_END, J_end >= 0, J_end <= DAY_END)
    s.add(K_start >= 0, K_start <= DAY_END, K_end >= 0, K_end <= DAY_END)

    # If not meeting, force zero interval
    s.add(Implies(Not(meet_J), And(J_start == 0, J_end == 0)))
    s.add(Implies(Not(meet_K), And(K_start == 0, K_end == 0)))

    # Meeting window and duration constraints
    s.add(Implies(meet_J, And(
        J_start >= J_start_avail,
        J_end <= J_end_avail,
        J_end - J_start >= J_min_dur,
        J_end >= J_start
    )))
    s.add(Implies(meet_K, And(
        K_start >= K_start_avail,
        K_end <= K_end_avail,
        K_end - K_start >= K_min_dur,
        K_end >= K_start
    )))

    # Travel feasibility from arrival
    s.add(Implies(meet_J, J_start >= arrival_time + travel[(arrival_loc, J_loc)]))
    s.add(Implies(meet_K, K_start >= arrival_time + travel[(arrival_loc, K_loc)]))

    # If both meetings are scheduled, enforce order with travel times and no overlap
    s.add(Implies(And(meet_J, meet_K),
                  Or(
                      K_start >= J_end + travel[(J_loc, K_loc)],
                      J_start >= K_end + travel[(K_loc, J_loc)]
                  )))
    # Tie order boolean to implications (not strict equivalence to keep flexibility)
    s.add(Implies(And(meet_J, meet_K, J_before_K), K_start >= J_end + travel[(J_loc, K_loc)]))
    s.add(Implies(And(meet_J, meet_K, Not(J_before_K)), J_start >= K_end + travel[(K_loc, J_loc)]))

    # Objectives
    num_met = If(meet_J, 1, 0) + If(meet_K, 1, 0)
    total_duration = If(meet_J, J_end - J_start, 0) + If(meet_K, K_end - K_start, 0)

    # Idle time (waiting) minimization
    initial_slack = If(And(meet_J, meet_K, J_before_K),
                       J_start - (arrival_time + travel[(arrival_loc, J_loc)]),
                       If(And(meet_J, meet_K, Not(J_before_K)),
                          K_start - (arrival_time + travel[(arrival_loc, K_loc)]),
                          If(And(meet_J, Not(meet_K)),
                             J_start - (arrival_time + travel[(arrival_loc, J_loc)]),
                             If(And(meet_K, Not(meet_J)),
                                K_start - (arrival_time + travel[(arrival_loc, K_loc)]),
                                0))))
    between_slack = If(And(meet_J, meet_K, J_before_K),
                       K_start - (J_end + travel[(J_loc, K_loc)]),
                       If(And(meet_J, meet_K, Not(J_before_K)),
                          J_start - (K_end + travel[(K_loc, J_loc)]),
                          0))
    # Ensure non-negative (should be by constraints)
    idle_time = If(initial_slack >= 0, initial_slack, 0) + If(between_slack >= 0, between_slack, 0)

    s.maximize(num_met)
    s.maximize(total_duration)
    s.minimize(idle_time)

    if s.check() != 1:  # not sat
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    m = s.model()

    itinerary = []

    if is_true(m.evaluate(meet_J)):
        js = m.evaluate(J_start).as_long()
        je = m.evaluate(J_end).as_long()
        itinerary.append({
            "action": "meet",
            "location": J_loc,
            "person": "Jason",
            "start_time": fmt_time(js),
            "end_time": fmt_time(je)
        })

    if is_true(m.evaluate(meet_K)):
        ks = m.evaluate(K_start).as_long()
        ke = m.evaluate(K_end).as_long()
        itinerary.append({
            "action": "meet",
            "location": K_loc,
            "person": "Kenneth",
            "start_time": fmt_time(ks),
            "end_time": fmt_time(ke)
        })

    # Sort by start times
    itinerary.sort(key=lambda x: int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1]))

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()