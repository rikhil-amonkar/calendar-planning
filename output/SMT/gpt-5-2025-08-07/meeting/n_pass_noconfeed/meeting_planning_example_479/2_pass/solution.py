import json
from z3 import Optimize, Int, If, And, Or, Implies, Sum, sat

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    Embarcadero = "Embarcadero"
    GGP = "Golden Gate Park"
    HA = "Haight-Ashbury"
    BV = "Bayview"
    PR = "Presidio"
    FD = "Financial District"

    # Travel times (minutes). Include self-to-self = 0 to avoid KeyErrors during constraint building.
    travel = {
        Embarcadero: {Embarcadero: 0, GGP:25, HA:21, BV:21, PR:20, FD:5},
        GGP:         {Embarcadero:25, GGP: 0, HA:7,  BV:23, PR:11, FD:26},
        HA:          {Embarcadero:20, GGP:7,  HA: 0, BV:18, PR:15, FD:21},
        BV:          {Embarcadero:19, GGP:22, HA:19, BV: 0, PR:31, FD:19},
        PR:          {Embarcadero:20, GGP:12, HA:15, BV:31, PR: 0, FD:23},
        FD:          {Embarcadero:4,  GGP:23, HA:19, BV:19, PR:22, FD: 0},
    }

    # Friends and constraints
    friends = [
        {
            "name": "Mary",
            "location": GGP,
            "avail_start": minutes(8,45),
            "avail_end": minutes(11,45),
            "min_dur": 45
        },
        {
            "name": "Kevin",
            "location": HA,
            "avail_start": minutes(10,15),
            "avail_end": minutes(16,15),
            "min_dur": 90
        },
        {
            "name": "Deborah",
            "location": BV,
            "avail_start": minutes(15,0),
            "avail_end": minutes(19,15),
            "min_dur": 120
        },
        {
            "name": "Stephanie",
            "location": PR,
            "avail_start": minutes(10,0),
            "avail_end": minutes(17,15),
            "min_dur": 120
        },
        {
            "name": "Emily",
            "location": FD,
            "avail_start": minutes(11,30),
            "avail_end": minutes(21,45),
            "min_dur": 105
        }
    ]

    # Starting point and time
    start_location = Embarcadero
    start_time = minutes(9,0)

    N = len(friends)

    # Z3 variables
    s = [Int(f"s_{i}") for i in range(N)]           # slot assignment: -1 for empty, else friend index 0..N-1
    start = [Int(f"start_{i}") for i in range(N)]   # meeting start time (minutes)
    end = [Int(f"end_{i}") for i in range(N)]       # meeting end time (minutes)

    o = Optimize()

    # Domain constraints and prefix (contiguous used slots then -1s)
    for i in range(N):
        o.add(And(s[i] >= -1, s[i] <= N-1))
    for i in range(1, N):
        o.add(Implies(s[i-1] == -1, s[i] == -1))
    # All-different among used slots
    for i in range(N):
        for j in range(i+1, N):
            o.add(Or(s[i] == -1, s[j] == -1, s[i] != s[j]))

    # Time constraints per slot
    for i in range(N):
        # If slot unused: start=end=0; if used: enforce positive duration and availability
        o.add(Implies(s[i] == -1, And(start[i] == 0, end[i] == 0)))
        o.add(Implies(s[i] != -1, And(start[i] >= 0, start[i] <= 24*60, end[i] >= 0, end[i] <= 24*60, end[i] > start[i])))
        # Availability and min durations per friend
        for f_idx, f in enumerate(friends):
            o.add(Implies(s[i] == f_idx, And(
                start[i] >= f["avail_start"],
                end[i] <= f["avail_end"],
                end[i] - start[i] >= f["min_dur"]
            )))

    # Travel from starting point to first meeting
    for f_idx, f in enumerate(friends):
        loc = f["location"]
        o.add(Implies(s[0] == f_idx, start[0] >= start_time + travel[start_location][loc]))

    # Travel between consecutive meetings
    for i in range(1, N):
        for fp_idx, fp in enumerate(friends):
            for fc_idx, fc in enumerate(friends):
                if fp_idx == fc_idx:
                    # Skip identical consecutive friends; not needed and avoids self-lookups
                    continue
                o.add(Implies(And(s[i-1] == fp_idx, s[i] == fc_idx),
                              start[i] >= end[i-1] + travel[fp["location"]][fc["location"]]))

    # Objective: maximize number of meetings, then maximize total duration
    used = [If(s[i] != -1, 1, 0) for i in range(N)]
    meet_count = Sum(used)
    total_duration = Sum([If(s[i] != -1, end[i] - start[i], 0) for i in range(N)])

    o.maximize(meet_count)
    o.maximize(total_duration)

    if o.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = o.model()

    itinerary = []
    for i in range(N):
        si = m.eval(s[i]).as_long()
        if si >= 0:
            f = friends[si]
            st = m.eval(start[i]).as_long()
            et = m.eval(end[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_str(st),
                "end_time": minutes_to_str(et)
            })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()