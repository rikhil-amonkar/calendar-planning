# pip install z3-solver
from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def solve_itinerary():
    # Time constants in minutes from 00:00
    NB_ARRIVAL = minutes(9, 0)

    # Availability windows
    MARK_START = minutes(13, 0)
    MARK_END   = minutes(17, 45)
    MARK_MIN   = 120

    KAREN_START = minutes(18, 45)
    KAREN_END   = minutes(20, 15)
    KAREN_MIN   = 90

    # Travel times (asymmetric) in minutes
    travel = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
    }

    # Z3 variables
    m_start, m_end, k_start, k_end = Ints("m_start m_end k_start k_end")
    meetM, meetK, orderMK = Bools("meetM meetK orderMK")  # orderMK=True means Mark before Karen

    o = Optimize()

    # Bounds for times
    for v in [m_start, m_end, k_start, k_end]:
        o.add(v >= 0, v <= 24 * 60)

    # Meeting window and minimum duration constraints (conditional on choosing to meet)
    o.add(Implies(meetM, And(m_start >= MARK_START,
                             m_end   <= MARK_END,
                             m_end - m_start >= MARK_MIN)))
    o.add(Implies(meetK, And(k_start >= KAREN_START,
                             k_end   <= KAREN_END,
                             k_end - k_start >= KAREN_MIN)))

    # Travel feasibility constraints
    # If meeting only Mark
    o.add(Implies(And(meetM, Not(meetK)),
                  NB_ARRIVAL + travel[("North Beach", "Embarcadero")] <= m_start))

    # If meeting only Karen
    o.add(Implies(And(meetK, Not(meetM)),
                  NB_ARRIVAL + travel[("North Beach", "Pacific Heights")] <= k_start))

    # If meeting both: enforce one of the two possible orders, with travel feasibility
    o.add(Implies(And(meetM, meetK, orderMK),
                  And(NB_ARRIVAL + travel[("North Beach", "Embarcadero")] <= m_start,
                      m_end + travel[("Embarcadero", "Pacific Heights")] <= k_start)))
    o.add(Implies(And(meetM, meetK, Not(orderMK)),
                  And(NB_ARRIVAL + travel[("North Beach", "Pacific Heights")] <= k_start,
                      k_end + travel[("Pacific Heights", "Embarcadero")] <= m_start)))

    # Objectives: maximize number of friends met, then total meeting time
    meet_count = If(meetM, 1, 0) + If(meetK, 1, 0)
    total_minutes = If(meetM, m_end - m_start, 0) + If(meetK, k_end - k_start, 0)
    o.maximize(meet_count)
    o.maximize(total_minutes)

    if o.check() != sat:
        return {"itinerary": []}

    model = o.model()

    itinerary = []
    if is_true(model[meetM]):
        ms = int(model[m_start].as_long())
        me = int(model[m_end].as_long())
        itinerary.append({
            "action": "meet",
            "person": "Mark",
            "start_time": to_hhmm(ms),
            "end_time": to_hhmm(me)
        })

    if is_true(model[meetK]):
        ks = int(model[k_start].as_long())
        ke = int(model[k_end].as_long())
        itinerary.append({
            "action": "meet",
            "person": "Karen",
            "start_time": to_hhmm(ks),
            "end_time": to_hhmm(ke)
        })

    # Sort by start time for readability
    itinerary.sort(key=lambda x: int(x["start_time"][:2]) * 60 + int(x["start_time"][3:5]))
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))