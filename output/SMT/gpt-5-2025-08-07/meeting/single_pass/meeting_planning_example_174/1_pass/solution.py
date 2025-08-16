# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Bool, If, And, Or, Not, is_true
import json

def minutes_to_hhmm(minutes_after_9):
    total = 9 * 60 + minutes_after_9
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

def solve():
    # Travel times (minutes)
    NH_to_PH = 8
    NH_to_MD = 13
    PH_to_NH = 8
    PH_to_MD = 15
    MD_to_NH = 12
    MD_to_PH = 16

    # Availability windows relative to 9:00 (in minutes)
    # Kenneth @ Mission District: 12:00–15:45 -> [180, 405]
    K_start_win = 180
    K_end_win = 405
    K_min_dur = 45

    # Thomas @ Pacific Heights: 15:30–19:15 -> [390, 615]
    T_start_win = 390
    T_end_win = 615
    T_min_dur = 75

    opt = Optimize()

    # Decision variables
    meetK = Bool("meetK")
    meetT = Bool("meetT")

    startK, endK = Int("startK"), Int("endK")
    startT, endT = Int("startT"), Int("endT")

    # Order variable: True => Kenneth before Thomas (K->T), False => Thomas before Kenneth (T->K)
    K_before_T = Bool("K_before_T")

    # Basic domains
    opt.add(startK >= 0, endK >= 0, startT >= 0, endT >= 0)

    # Meeting window and duration constraints (conditional on meeting them)
    opt.add(Implies(meetK, And(startK >= K_start_win,
                               endK <= K_end_win,
                               endK - startK >= K_min_dur)))
    opt.add(Implies(meetT, And(startT >= T_start_win,
                               endT <= T_end_win,
                               endT - startT >= T_min_dur)))

    # Initial travel from Nob Hill at 9:00 to the first meeting
    # If K is first or only meeting:
    opt.add(Implies(And(meetK, Or(Not(meetT), K_before_T)), startK >= NH_to_MD))
    # If T is first or only meeting:
    opt.add(Implies(And(meetT, Or(Not(meetK), Not(K_before_T))), startT >= NH_to_PH))

    # Travel between meetings if both are scheduled
    # If K before T, respect MD->PH travel
    opt.add(Implies(And(meetK, meetT, K_before_T), startT >= endK + MD_to_PH))
    # If T before K, respect PH->MD travel
    opt.add(Implies(And(meetK, meetT, Not(K_before_T)), startK >= endT + PH_to_MD))

    # Objective 1: maximize number of friends met
    count_meetings = If(meetK, 1, 0) + If(meetT, 1, 0)
    opt.maximize(count_meetings)

    # Objective 2: minimize the finish time of the last meeting (for earlier wrap-up),
    # subordinate to meeting as many friends as possible
    last_end = If(And(meetK, meetT, K_before_T), endT,
               If(And(meetK, meetT, Not(K_before_T)), endK,
               If(meetT, endT,
               If(meetK, endK, 0))))
    opt.minimize(last_end)

    if opt.check() != sat:
        # No feasible schedule
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    meet_k = is_true(m.evaluate(meetK))
    meet_t = is_true(m.evaluate(meetT))

    itinerary = []
    if meet_k:
        sK = m.evaluate(startK).as_long()
        eK = m.evaluate(endK).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_hhmm(sK),
            "end_time": minutes_to_hhmm(eK)
        })

    if meet_t:
        sT = m.evaluate(startT).as_long()
        eT = m.evaluate(endT).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Thomas",
            "start_time": minutes_to_hhmm(sT),
            "end_time": minutes_to_hhmm(eT)
        })

    # Sort chronologically by start_time
    itinerary.sort(key=lambda x: x["start_time"])

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    solve()