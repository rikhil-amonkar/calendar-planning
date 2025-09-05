import json
from z3 import Optimize, Int, If, And, Or, Implies, Sum, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    BV, RH, AS, NB, FD = 0, 1, 2, 3, 4
    location_names = {
        RH: "Russian Hill",
        AS: "Alamo Square",
        NB: "North Beach",
        FD: "Financial District",
        BV: "Bayview",
    }

    # People enumeration
    JOSEPH, NANCY, JASON, JEFFREY = 0, 1, 2, 3
    person_names = {
        JOSEPH: "Joseph",
        NANCY: "Nancy",
        JASON: "Jason",
        JEFFREY: "Jeffrey",
    }
    person_location = {
        JOSEPH: RH,
        NANCY: AS,
        JASON: NB,
        JEFFREY: FD,
    }

    # Availability windows and minimum durations (in minutes since midnight)
    avail_start = {
        JOSEPH: minutes(8, 30),
        NANCY: minutes(11, 0),
        JASON: minutes(16, 45),
        JEFFREY: minutes(10, 30),
    }
    avail_end = {
        JOSEPH: minutes(19, 15),
        NANCY: minutes(16, 0),
        JASON: minutes(21, 45),
        JEFFREY: minutes(15, 45),
    }
    min_dur = {
        JOSEPH: 60,
        NANCY: 90,
        JASON: 15,
        JEFFREY: 45,
    }

    # Travel times in minutes (directed)
    # Locations: 0 BV, 1 RH, 2 AS, 3 NB, 4 FD
    T = [[0 for _ in range(5)] for _ in range(5)]
    # Bayview to others
    T[BV][RH] = 23
    T[BV][AS] = 16
    T[BV][NB] = 21
    T[BV][FD] = 19
    # Others to Bayview
    T[RH][BV] = 23
    T[AS][BV] = 16
    T[NB][BV] = 22
    T[FD][BV] = 19
    # Between non-Bayview locations
    T[RH][AS] = 15
    T[RH][NB] = 5
    T[RH][FD] = 11

    T[AS][RH] = 13
    T[AS][NB] = 15
    T[AS][FD] = 17

    T[NB][RH] = 4
    T[NB][AS] = 16
    T[NB][FD] = 8

    T[FD][RH] = 10
    T[FD][AS] = 17
    T[FD][NB] = 7

    # Same-location travel is 0
    for i in range(5):
        T[i][i] = 0

    # Start at Bayview at 9:00
    start_at_bv = minutes(9, 0)

    # We'll plan up to 4 positions in the itinerary (one per person max)
    max_positions = 4
    NONE = 4  # special code for "no meeting" at that position

    # Z3 variables
    opt = Optimize()
    pos = [Int(f"pos_{i}") for i in range(max_positions)]  # which person index at each position, or NONE
    start = [Int(f"start_{i}") for i in range(max_positions)]
    end = [Int(f"end_{i}") for i in range(max_positions)]

    # Domains
    for i in range(max_positions):
        opt.add(And(pos[i] >= 0, pos[i] <= NONE))
        opt.add(And(start[i] >= 0, start[i] <= 24*60))
        opt.add(And(end[i] >= 0, end[i] <= 24*60))

    # Packing constraint: once NONE appears, all following positions are NONE
    for i in range(1, max_positions):
        opt.add(Implies(pos[i-1] == NONE, pos[i] == NONE))

    # At most one occurrence per person
    persons = [JOSEPH, NANCY, JASON, JEFFREY]
    for p in persons:
        opt.add(Sum([If(pos[i] == p, 1, 0) for i in range(max_positions)]) <= 1)

    # When NONE, times are zero; otherwise meeting constraints
    for i in range(max_positions):
        # If NONE, times are 0
        opt.add(Implies(pos[i] == NONE, And(start[i] == 0, end[i] == 0)))
        # If not NONE, end >= start
        opt.add(Implies(pos[i] != NONE, end[i] >= start[i]))

        # Availability windows and minimum durations per assigned person
        for p in persons:
            opt.add(Implies(
                pos[i] == p,
                And(
                    start[i] >= avail_start[p],
                    end[i] <= avail_end[p],
                    end[i] - start[i] >= min_dur[p]
                )
            ))

    # Travel constraints from Bayview to first meeting
    for p in persons:
        opt.add(Implies(pos[0] == p, start[0] >= start_at_bv + T[BV][person_location[p]]))

    # Travel constraints between consecutive meetings
    for i in range(1, max_positions):
        for p_prev in persons:
            for p_cur in persons:
                opt.add(Implies(
                    And(pos[i-1] == p_prev, pos[i] == p_cur),
                    start[i] >= end[i-1] + T[person_location[p_prev]][person_location[p_cur]]
                ))

    # Objective 1: maximize number of meetings (active positions)
    num_meetings = Sum([If(pos[i] != NONE, 1, 0) for i in range(max_positions)])
    opt.maximize(num_meetings)

    # Objective 2: maximize total meeting duration
    total_duration = Sum([end[i] - start[i] for i in range(max_positions)])
    opt.maximize(total_duration)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))
        return

    model = opt.model()

    itinerary = []
    for i in range(max_positions):
        pi = model[pos[i]].as_long()
        if pi == NONE:
            break
        si = model[start[i]].as_long()
        ei = model[end[i]].as_long()
        itinerary.append({
            "action": "meet",
            "location": location_names[person_location[pi]],
            "person": person_names[pi],
            "start_time": fmt_time(si),
            "end_time": fmt_time(ei),
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()