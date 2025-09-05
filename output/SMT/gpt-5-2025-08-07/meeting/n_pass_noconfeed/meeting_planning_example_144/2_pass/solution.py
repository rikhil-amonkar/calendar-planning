import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Sum, sat, is_true

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    C, M, F = 0, 1, 2
    loc_names = {M: "Mission District", F: "Financial District"}
    person_loc = {"Laura": M, "Anthony": F}

    # Travel times (minutes)
    T = [[0]*3 for _ in range(3)]
    T[C][M] = 7
    T[C][F] = 20
    T[M][C] = 7
    T[M][F] = 17
    T[F][C] = 23
    T[F][M] = 17

    # Start at The Castro at 9:00
    start_time = 9*60
    start_loc = C

    # Availability windows (minutes from midnight)
    L_start, L_end = 12*60 + 15, 19*60 + 45  # 12:15 - 19:45
    A_start, A_end = 12*60 + 30, 14*60 + 45  # 12:30 - 14:45

    # Minimum meeting durations
    L_min = 75
    A_min = 30

    # Solver
    opt = Optimize()

    # Decision variables
    meetL = Bool("meetL")
    meetA = Bool("meetA")
    l_before_a = Bool("l_before_a")  # True if Laura before Anthony

    sL = Int("sL")
    eL = Int("eL")
    sA = Int("sA")
    eA = Int("eA")

    # Domains
    for v in [sL, eL, sA, eA]:
        opt.add(v >= 0, v <= 24*60)

    # If not meeting someone, times are zero
    opt.add(Implies(Not(meetL), And(sL == 0, eL == 0)))
    opt.add(Implies(Not(meetA), And(sA == 0, eA == 0)))

    # Availability and duration constraints
    opt.add(Implies(meetL, And(sL >= L_start, eL <= L_end, eL - sL >= L_min)))
    opt.add(Implies(meetA, And(sA >= A_start, eA <= A_end, eA - sA >= A_min)))

    # Initial travel constraints depending on which meeting is first/only
    opt.add(Implies(And(meetL, Not(meetA)), sL >= start_time + T[start_loc][M]))
    opt.add(Implies(And(meetA, Not(meetL)), sA >= start_time + T[start_loc][F]))

    opt.add(Implies(And(meetL, meetA, l_before_a), sL >= start_time + T[start_loc][M]))
    opt.add(Implies(And(meetL, meetA, Not(l_before_a)), sA >= start_time + T[start_loc][F]))

    # Sequencing and travel between meetings
    opt.add(Implies(And(meetL, meetA, l_before_a), sA >= eL + T[M][F]))
    opt.add(Implies(And(meetL, meetA, Not(l_before_a)), sL >= eA + T[F][M]))

    # Objective: maximize number of friends met, then minimize makespan (finish time)
    meet_count = If(meetL, 1, 0) + If(meetA, 1, 0)
    makespan = If(And(meetL, meetA),
                  If(eL > eA, eL, eA),
                  If(meetL, eL, If(meetA, eA, start_time)))
    opt.maximize(meet_count)
    opt.minimize(makespan)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    meetL_val = is_true(m.eval(meetL, model_completion=True))
    meetA_val = is_true(m.eval(meetA, model_completion=True))

    itinerary = []

    if meetL_val:
        sL_val = m.eval(sL, model_completion=True).as_long()
        eL_val = m.eval(eL, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": loc_names[M],
            "person": "Laura",
            "start_time": fmt_time(sL_val),
            "end_time": fmt_time(eL_val),
            "_sort": sL_val
        })

    if meetA_val:
        sA_val = m.eval(sA, model_completion=True).as_long()
        eA_val = m.eval(eA, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": loc_names[F],
            "person": "Anthony",
            "start_time": fmt_time(sA_val),
            "end_time": fmt_time(eA_val),
            "_sort": sA_val
        })

    # Sort by start time
    itinerary.sort(key=lambda x: x["_sort"])
    for item in itinerary:
        item.pop("_sort", None)

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()