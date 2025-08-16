# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, And, Or, Implies, If, Not, sat
import json

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def solve_itinerary():
    # Time constants (minutes from midnight)
    NB_ARRIVE = 9 * 60  # 09:00 = 540
    # Availability windows
    EMILY_START = 16 * 60        # 16:00 = 960
    EMILY_END   = 17 * 60 + 15   # 17:15 = 1035
    EMILY_MIN   = 45

    MARG_START = 19 * 60        # 19:00 = 1140
    MARG_END   = 21 * 60        # 21:00 = 1260
    MARG_MIN   = 120

    # Travel times (asymmetric)
    NB_to_US  = 7
    NB_to_RH  = 4
    US_to_NB  = 10
    RH_to_NB  = 5
    US_to_RH  = 13
    RH_to_US  = 11

    opt = Optimize()

    # Variables
    E_start = Int("E_start")
    E_end   = Int("E_end")
    M_start = Int("M_start")
    M_end   = Int("M_end")
    meet_E  = Bool("meet_E")
    meet_M  = Bool("meet_M")

    # Bounds to keep times reasonable
    for v in [E_start, E_end, M_start, M_end]:
        opt.add(v >= 0, v <= 24*60)

    # Emily constraints
    opt.add(Implies(meet_E, And(
        E_start >= EMILY_START,
        E_end   <= EMILY_END,
        E_end > E_start,
        E_end - E_start >= EMILY_MIN
    )))
    # If not meeting, collapse times (arbitrary, to keep them fixed)
    opt.add(Implies(Not(meet_E), And(E_start == 0, E_end == 0)))

    # Margaret constraints
    opt.add(Implies(meet_M, And(
        M_start >= MARG_START,
        M_end   <= MARG_END,
        M_end > M_start,
        M_end - M_start >= MARG_MIN
    )))
    opt.add(Implies(Not(meet_M), And(M_start == 0, M_end == 0)))

    # Sequencing and travel feasibility
    # If both meetings occur, enforce feasible order with travel times,
    # and reachability from North Beach at 09:00.
    both = And(meet_E, meet_M)
    e_before_m = And(E_end + US_to_RH <= M_start, E_start >= NB_ARRIVE + NB_to_US)
    m_before_e = And(M_end + RH_to_US <= E_start, M_start >= NB_ARRIVE + NB_to_RH)
    opt.add(Implies(both, Or(e_before_m, m_before_e)))

    # If only one meeting occurs, ensure it's reachable from NB at 09:00
    opt.add(Implies(And(meet_E, Not(meet_M)), E_start >= NB_ARRIVE + NB_to_US))
    opt.add(Implies(And(meet_M, Not(meet_E)), M_start >= NB_ARRIVE + NB_to_RH))

    # Objective: maximize number of friends met, then maximize total meeting time
    opt.maximize(If(meet_E, 1, 0) + If(meet_M, 1, 0))
    opt.maximize(If(meet_E, E_end - E_start, 0) + If(meet_M, M_end - M_start, 0))

    if opt.check() != sat:
        return {"itinerary": []}

    model = opt.model()

    itinerary = []
    if model.eval(meet_E):
        itinerary.append({
            "action": "meet",
            "person": "Emily",
            "start_time": minutes_to_hhmm(model.eval(E_start).as_long()),
            "end_time": minutes_to_hhmm(model.eval(E_end).as_long())
        })
    if model.eval(meet_M):
        itinerary.append({
            "action": "meet",
            "person": "Margaret",
            "start_time": minutes_to_hhmm(model.eval(M_start).as_long()),
            "end_time": minutes_to_hhmm(model.eval(M_end).as_long())
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))