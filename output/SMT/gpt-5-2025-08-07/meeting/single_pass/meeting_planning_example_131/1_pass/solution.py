# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def solve_itinerary():
    # Time reference: minutes from 00:00
    # Locations
    PH, PR, MD = "Pacific Heights", "Presidio", "Marina District"

    # Travel times (minutes)
    travel = {
        (PH, PR): 11,
        (PR, PH): 11,
        (PH, MD): 6,
        (MD, PH): 7,
        (PR, MD): 10,
        (MD, PR): 10,
    }

    # Day start
    start_loc = PH
    start_time = 9 * 60  # 09:00 -> 540

    # Friend availability and minimum durations
    # Jason at Presidio: 10:00-16:15, min 90
    J_loc, J_start, J_end, J_min = PR, 10 * 60, 16 * 60 + 15, 90
    # Kenneth at Marina District: 15:30-16:45, min 45
    K_loc, K_start, K_end, K_min = MD, 15 * 60 + 30, 16 * 60 + 45, 45

    # Z3 variables
    sj, ej = Ints('sj ej')  # Jason start/end
    sk, ek = Ints('sk ek')  # Kenneth start/end
    meet_j, meet_k = Bools('meet_j meet_k')
    j_first = Bool('j_first')  # If both meetings happen, Jason before Kenneth?

    o = Optimize()

    # Bounds to help solver
    for v in [sj, ej, sk, ek]:
        o.add(v >= 0, v <= 24 * 60)

    # Jason constraints if meeting
    o.add(Implies(meet_j, And(
        sj >= J_start,
        ej <= J_end,
        ej > sj,
        ej - sj >= J_min
    )))
    # Kenneth constraints if meeting
    o.add(Implies(meet_k, And(
        sk >= K_start,
        ek <= K_end,
        ek > sk,
        ek - sk >= K_min
    )))

    # Travel/time ordering constraints when both meetings occur
    # If both and Jason first: Jason -> Kenneth with travel PR->MD
    o.add(Implies(And(meet_j, meet_k, j_first),
                  And(ej + travel[(PR, MD)] <= sk,
                      sj >= start_time + travel[(start_loc, PR)])))
    # If both and Kenneth first: Kenneth -> Jason with travel MD->PR
    o.add(Implies(And(meet_j, meet_k, Not(j_first)),
                  And(ek + travel[(MD, PR)] <= sj,
                      sk >= start_time + travel[(start_loc, MD)])))

    # If only Jason is met: must be reachable from start
    o.add(Implies(And(meet_j, Not(meet_k)),
                  sj >= start_time + travel[(start_loc, PR)]))
    # If only Kenneth is met: must be reachable from start
    o.add(Implies(And(meet_k, Not(meet_j)),
                  sk >= start_time + travel[(start_loc, MD)]))

    # Primary objective: maximize number of unique friends met
    count_friends = If(meet_j, 1, 0) + If(meet_k, 1, 0)
    o.maximize(count_friends)

    # Secondary: maximize total meeting time
    total_dur = If(meet_j, ej - sj, 0) + If(meet_k, ek - sk, 0)
    o.maximize(total_dur)

    # Tertiary: maximize Kenneth's duration (prefer full window for tie-break)
    o.maximize(If(meet_k, ek - sk, 0))

    # Quaternary: minimize Jason start time (prefer earliest feasible)
    o.minimize(sj)

    if o.check() != sat:
        return {"itinerary": []}

    m = o.model()

    itinerary = []

    if m.evaluate(meet_j).is_true():
        itinerary.append({
            "action": "meet",
            "person": "Jason",
            "start_time": fmt_time(m.evaluate(sj).as_long()),
            "end_time": fmt_time(m.evaluate(ej).as_long())
        })

    if m.evaluate(meet_k).is_true():
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": fmt_time(m.evaluate(sk).as_long()),
            "end_time": fmt_time(m.evaluate(ek).as_long())
        })

    # Sort chronologically
    itinerary.sort(key=lambda x: x["start_time"])

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))