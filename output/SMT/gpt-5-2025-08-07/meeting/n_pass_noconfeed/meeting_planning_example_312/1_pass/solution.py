"SOLUTION:"
from z3 import Int, Bool, Optimize, If, And, Or, Not, Implies, Sum, is_true
import json

def to_min(tstr):
    # expects 'H:MM' possibly without leading zero
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    RD = "Richmond District"
    SD = "Sunset District"
    HA = "Haight-Ashbury"
    MD = "Mission District"
    GGP = "Golden Gate Park"

    # Travel times (minutes), possibly asymmetric
    travel = {
        (RD, SD): 11,
        (RD, HA): 10,
        (RD, MD): 20,
        (RD, GGP): 9,
        (SD, RD): 12,
        (SD, HA): 15,
        (SD, MD): 24,
        (SD, GGP): 11,
        (HA, RD): 10,
        (HA, SD): 15,
        (HA, MD): 11,  # given 11; from Haight-Ashbury to Mission District: 11 (note asymmetry; below we also have Mission->Haight: 12)
        (HA, GGP): 7,
        (MD, RD): 20,
        (MD, SD): 24,
        (MD, HA): 12,
        (MD, GGP): 17,
        (GGP, RD): 7,
        (GGP, SD): 10,
        (GGP, HA): 7,
        (GGP, MD): 17,
    }

    # Arrive at Richmond District at 9:00
    arrival_loc = RD
    arrival_time = to_min("9:00")

    # Friends and constraints
    friends = {
        "Sarah": {
            "location": SD,
            "avail_start": to_min("10:45"),
            "avail_end": to_min("19:00"),
            "min_duration": 30,
        },
        "Richard": {
            "location": HA,
            "avail_start": to_min("11:45"),
            "avail_end": to_min("15:45"),
            "min_duration": 90,
        },
        "Elizabeth": {
            "location": MD,
            "avail_start": to_min("11:00"),
            "avail_end": to_min("17:15"),
            "min_duration": 120,
        },
        "Michelle": {
            "location": GGP,
            "avail_start": to_min("18:15"),
            "avail_end": to_min("20:45"),
            "min_duration": 90,
        },
    }

    people = list(friends.keys())

    opt = Optimize()

    # Decision variables
    start = {p: Int(f"start_{p}") for p in people}
    end = {p: Int(f"end_{p}") for p in people}
    attend = {p: Bool(f"attend_{p}") for p in people}

    # Bounds and availability/min-duration constraints
    for p in people:
        loc = friends[p]["location"]
        a_s = friends[p]["avail_start"]
        a_e = friends[p]["avail_end"]
        min_d = friends[p]["min_duration"]

        opt.add(start[p] >= 0, start[p] <= 24*60)
        opt.add(end[p] >= 0, end[p] <= 24*60)

        # If attending, respect window and duration; else start=end (zero-length inactive)
        opt.add(Implies(attend[p], And(start[p] >= a_s, end[p] <= a_e, end[p] - start[p] >= min_d)))
        opt.add(Implies(Not(attend[p]), start[p] == end[p]))

        # Arrival feasibility from arrival point
        t_from_arrival = travel[(arrival_loc, loc)]
        opt.add(Implies(attend[p], start[p] >= arrival_time + t_from_arrival))

    # Pairwise ordering and travel feasibility between meetings
    before = {}
    for i in range(len(people)):
        for j in range(len(people)):
            if i == j:
                continue
            pi, pj = people[i], people[j]
            before[(pi, pj)] = Bool(f"before_{pi}_{pj}")

    for i in range(len(people)):
        for j in range(i+1, len(people)):
            p = people[i]
            q = people[j]
            # If both attended, exactly one direction must hold
            opt.add(Implies(And(attend[p], attend[q]), Or(before[(p, q)], before[(q, p)])))
            # Anti-symmetry
            opt.add(Implies(before[(p, q)], Not(before[(q, p)])))
            opt.add(Implies(before[(q, p)], Not(before[(p, q)])))

            # Temporal constraints with travel times
            loc_p = friends[p]["location"]
            loc_q = friends[q]["location"]
            opt.add(Implies(And(attend[p], attend[q], before[(p, q)]), start[q] >= end[p] + travel[(loc_p, loc_q)]))
            opt.add(Implies(And(attend[p], attend[q], before[(q, p)]), start[p] >= end[q] + travel[(loc_q, loc_p)]))

    # Objectives:
    # 1) Maximize number of friends met
    total_meetings = Sum([If(attend[p], 1, 0) for p in people])
    opt.maximize(total_meetings)

    # 2) Maximize total meeting time
    total_duration = Sum([If(attend[p], end[p] - start[p], 0) for p in people])
    opt.maximize(total_duration)

    # Solve
    if opt.check() != 1:
        # No solution
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    # Build itinerary from attended meetings
    meetings = []
    for p in people:
        if is_true(model[attend[p]]):
            s = model[start[p]].as_long()
            e = model[end[p]].as_long()
            meetings.append({
                "action": "meet",
                "location": friends[p]["location"],
                "person": p,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e),
                "_start_min": s  # helper for sorting
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["_start_min"])
    # Remove helper
    for m in meetings:
        m.pop("_start_min", None)

    output = {"itinerary": meetings}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()