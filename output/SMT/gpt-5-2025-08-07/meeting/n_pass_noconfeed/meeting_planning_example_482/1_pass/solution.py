import json
from z3 import Optimize, Int, Bool, Sum, If, And, Or, Not, Xor, sat

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    HA = "Haight-Ashbury"
    MD = "Mission District"
    BV = "Bayview"
    PH = "Pacific Heights"
    RH = "Russian Hill"
    FW = "Fisherman's Wharf"

    # Travel times in minutes (directed)
    travel = {
        (HA, MD): 11,
        (HA, BV): 18,
        (HA, PH): 12,
        (HA, RH): 17,
        (HA, FW): 23,
        (MD, HA): 12,
        (MD, BV): 15,
        (MD, PH): 16,
        (MD, RH): 15,
        (MD, FW): 22,
        (BV, HA): 19,
        (BV, MD): 13,
        (BV, PH): 23,
        (BV, RH): 23,
        (BV, FW): 25,
        (PH, HA): 11,
        (PH, MD): 15,
        (PH, BV): 22,
        (PH, RH): 7,
        (PH, FW): 13,
        (RH, HA): 17,
        (RH, MD): 16,
        (RH, BV): 23,
        (RH, PH): 7,
        (RH, FW): 7,
        (FW, HA): 22,
        (FW, MD): 22,
        (FW, BV): 26,
        (FW, PH): 12,
        (FW, RH): 7,
    }

    def t(a, b):
        return travel[(a, b)]

    # Arrival at Haight-Ashbury at 9:00 (540 minutes)
    start_location = HA
    arrival_time = 9 * 60

    # People data: name: {location, availability (start,end), min_duration}
    people = {
        "Stephanie": {
            "location": MD,
            "avail_start": 8*60 + 15,   # 8:15
            "avail_end": 13*60 + 45,    # 13:45
            "min_dur": 90
        },
        "Sandra": {
            "location": BV,
            "avail_start": 13*60,       # 13:00
            "avail_end": 19*60 + 30,    # 19:30
            "min_dur": 15
        },
        "Richard": {
            "location": PH,
            "avail_start": 7*60 + 15,   # 7:15
            "avail_end": 10*60 + 15,    # 10:15
            "min_dur": 75
        },
        "Brian": {
            "location": RH,
            "avail_start": 12*60 + 15,  # 12:15
            "avail_end": 16*60,         # 16:00
            "min_dur": 120
        },
        "Jason": {
            "location": FW,
            "avail_start": 8*60 + 30,   # 8:30
            "avail_end": 17*60 + 45,    # 17:45
            "min_dur": 60
        }
    }

    names = list(people.keys())

    # Z3 variables
    s = Optimize()

    start = {n: Int(f"start_{n}") for n in names}
    end = {n: Int(f"end_{n}") for n in names}
    meet = {n: Bool(f"meet_{n}") for n in names}

    # Time bounds and individual constraints
    for n in names:
        loc = people[n]["location"]
        avail_s = people[n]["avail_start"]
        avail_e = people[n]["avail_end"]
        min_d = people[n]["min_dur"]

        # Domain bounds
        s.add(start[n] >= 0, start[n] <= 24*60)
        s.add(end[n] >= 0, end[n] <= 24*60)

        # If meeting, must be within availability and meet duration
        s.add(If(meet[n],
                 And(start[n] >= avail_s,
                     end[n] <= avail_e,
                     end[n] - start[n] >= min_d),
                 end[n] == start[n]))  # if not meeting, tie end to start

        # Cannot start before arriving from initial location
        s.add(start[n] >= arrival_time + t(start_location, loc))

    # Pairwise disjunctive constraints (no overlap + travel time between)
    before = {}
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            ni, nj = names[i], names[j]
            loc_i = people[ni]["location"]
            loc_j = people[nj]["location"]

            b_ij = Bool(f"before_{ni}_{nj}")
            b_ji = Bool(f"before_{nj}_{ni}")
            before[(ni, nj)] = b_ij
            before[(nj, ni)] = b_ji

            # If both are met, exactly one order holds; else none holds
            s.add(If(And(meet[ni], meet[nj]),
                     Xor(b_ij, b_ji),
                     And(Not(b_ij), Not(b_ji))))

            # Travel feasibility when ordered
            s.add(Implies(b_ij, And(end[ni] + t(loc_i, loc_j) <= start[nj], meet[ni], meet[nj])))
            s.add(Implies(b_ji, And(end[nj] + t(loc_j, loc_i) <= start[ni], meet[ni], meet[nj])))

    # Objectives
    num_met = Sum([If(meet[n], 1, 0) for n in names])
    s.maximize(num_met)

    # Minimize latest end time among meetings (use 540 as baseline if not met)
    latest_end = Int("latest_end")
    s.add(latest_end >= 0, latest_end <= 24*60)
    for n in names:
        s.add(latest_end >= If(meet[n], end[n], arrival_time))
    s.minimize(latest_end)

    # As a tie-breaker, minimize sum of start times for meetings to prefer earlier schedules
    sum_starts = Sum([If(meet[n], start[n], 0) for n in names])
    s.minimize(sum_starts)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    itinerary = []
    for n in names:
        if m.evaluate(meet[n], model_completion=True):
            st = m.evaluate(start[n]).as_long()
            en = m.evaluate(end[n]).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[n]["location"],
                "person": n,
                "start_time": fmt_time(st),
                "end_time": fmt_time(en)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()