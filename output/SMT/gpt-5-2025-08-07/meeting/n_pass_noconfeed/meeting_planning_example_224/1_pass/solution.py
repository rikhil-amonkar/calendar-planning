import json
from z3 import Optimize, Int, Bool, And, Or, If, Implies, Sum, Not, is_true

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    FW = "Fisherman's Wharf"
    GGP = "Golden Gate Park"
    PR = "Presidio"
    RD = "Richmond District"

    # Travel times (minutes), directional
    t = {}
    t[(FW, GGP)] = 25
    t[(FW, PR)] = 17
    t[(FW, RD)] = 18

    t[(GGP, FW)] = 24
    t[(GGP, PR)] = 11
    t[(GGP, RD)] = 7

    t[(PR, FW)] = 19
    t[(PR, GGP)] = 12
    t[(PR, RD)] = 7

    t[(RD, FW)] = 18
    t[(RD, GGP)] = 9
    t[(RD, PR)] = 7

    # Start info
    start_location = FW
    start_time = 9 * 60  # 9:00 -> 540

    # People constraints
    people = [
        {
            "name": "Melissa",
            "location": GGP,
            "avail_start": 8 * 60 + 30,   # 8:30 -> 510
            "avail_end": 20 * 60,         # 20:00 -> 1200
            "min_duration": 15
        },
        {
            "name": "Nancy",
            "location": PR,
            "avail_start": 19 * 60 + 45,  # 19:45 -> 1185
            "avail_end": 22 * 60,         # 22:00 -> 1320
            "min_duration": 105
        },
        {
            "name": "Emily",
            "location": RD,
            "avail_start": 16 * 60 + 45,  # 16:45 -> 1005
            "avail_end": 22 * 60,         # 22:00 -> 1320
            "min_duration": 120
        },
    ]

    # Z3 variables per person
    opt = Optimize()
    s_vars = {}
    e_vars = {}
    meet_vars = {}

    for p in people:
        s = Int(f"s_{p['name']}")
        e = Int(f"e_{p['name']}")
        meet = Bool(f"meet_{p['name']}")
        s_vars[p['name']] = s
        e_vars[p['name']] = e
        meet_vars[p['name']] = meet

        # Domain bounds
        opt.add(s >= 0, s <= 24 * 60)
        opt.add(e >= 0, e <= 24 * 60)
        opt.add(e >= s)  # always true

        # If meeting occurs, respect availability window and min duration
        opt.add(Implies(meet, And(
            s >= p['avail_start'],
            e <= p['avail_end'],
            e - s >= p['min_duration']
        )))
        # If not meeting, no duration
        opt.add(Implies(Not(meet), e == s))

        # Must be reachable from starting point if meeting
        opt.add(Implies(meet, s >= start_time + t[(start_location, p['location'])]))

    # Pairwise separation with travel times between meetings
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            si, ei, mi = s_vars[pi['name']], e_vars[pi['name']], meet_vars[pi['name']]
            sj, ej, mj = s_vars[pj['name']], e_vars[pj['name']], meet_vars[pj['name']]
            tij = t[(pi['location'], pj['location'])]
            tji = t[(pj['location'], pi['location'])]

            # If both meetings occur, enforce non-overlap with travel time
            opt.add(Implies(And(mi, mj), Or(
                sj >= ei + tij,  # i before j
                si >= ej + tji   # j before i
            )))

    # Objectives: maximize number of friends met, then total meeting duration
    total_people = Sum([If(meet_vars[p['name']], 1, 0) for p in people])
    total_minutes = Sum([If(meet_vars[p['name']], e_vars[p['name']] - s_vars[p['name']], 0) for p in people])
    opt.maximize(total_people)
    opt.maximize(total_minutes)

    if opt.check() != 1:  # sat
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Build itinerary from model
    meetings = []
    for p in people:
        if is_true(m.evaluate(meet_vars[p['name']])):  # met
            s_val = m.evaluate(s_vars[p['name']]).as_long()
            e_val = m.evaluate(e_vars[p['name']]).as_long()
            meetings.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_str(s_val),
                "end_time": minutes_to_str(e_val),
                "_start_minutes": s_val  # for sorting, will remove later
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["_start_minutes"])
    for item in meetings:
        item.pop("_start_minutes", None)

    print(json.dumps({"itinerary": meetings}, ensure_ascii=False))

if __name__ == "__main__":
    main()