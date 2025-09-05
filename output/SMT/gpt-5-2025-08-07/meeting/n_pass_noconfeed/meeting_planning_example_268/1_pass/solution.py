import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    GGP = "Golden Gate Park"
    AS = "Alamo Square"
    PR = "Presidio"
    RH = "Russian Hill"

    # Travel times (minutes), directed
    travel = {
        (GGP, AS): 10,
        (GGP, PR): 11,
        (GGP, RH): 19,
        (AS, GGP): 9,
        (AS, PR): 18,
        (AS, RH): 13,
        (PR, GGP): 12,
        (PR, AS): 18,
        (PR, RH): 14,
        (RH, GGP): 21,
        (RH, AS): 15,
        (RH, PR): 14,
    }

    # Start time at Golden Gate Park
    start_at = minutes(9, 0)

    # People constraints
    people = {
        "Timothy": {
            "location": AS,
            "window_start": minutes(12, 0),
            "window_end": minutes(16, 15),
            "min_duration": 105
        },
        "Mark": {
            "location": PR,
            "window_start": minutes(18, 45),
            "window_end": minutes(21, 0),
            "min_duration": 60
        },
        "Joseph": {
            "location": RH,
            "window_start": minutes(16, 45),
            "window_end": minutes(21, 30),
            "min_duration": 60
        }
    }

    # Z3 variables
    opt = Optimize()

    start = {}
    end = {}
    attend = {}

    for p in people:
        start[p] = Int(f"{p}_start")
        end[p] = Int(f"{p}_end")
        attend[p] = Bool(f"{p}_attend")

        # General bounds
        opt.add(start[p] >= 0, end[p] >= 0, end[p] >= start[p])

        # If attending, must be within availability window and meet minimum duration
        ws = people[p]["window_start"]
        we = people[p]["window_end"]
        md = people[p]["min_duration"]

        # Must be physically reachable from the starting location
        loc = people[p]["location"]
        opt.add(Implies(attend[p], start[p] >= start_at + travel[(GGP, loc)]))

        # Window and duration constraints when attending
        opt.add(Implies(attend[p], And(start[p] >= ws, end[p] <= we, end[p] - start[p] >= md)))
        # If not attending, collapse meeting to zero duration
        opt.add(Implies(Not(attend[p]), end[p] == start[p]))

    # Pairwise ordering and travel constraints
    persons = list(people.keys())

    # For each unordered pair, define an order variable: i_before_j
    order_vars = {}
    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            pi = persons[i]
            pj = persons[j]
            order_vars[(pi, pj)] = Bool(f"{pi}_before_{pj}")
            # If both attended, exactly one order holds (pi before pj) or (pj before pi)
            opt.add(Implies(And(attend[pi], attend[pj]), Or(order_vars[(pi, pj)], Not(order_vars[(pi, pj)]))))
            # Enforce ordering implications with travel times
            li = people[pi]["location"]
            lj = people[pj]["location"]
            opt.add(Implies(And(attend[pi], attend[pj], order_vars[(pi, pj)]),
                            start[pj] >= end[pi] + travel[(li, lj)]))
            opt.add(Implies(And(attend[pi], attend[pj], Not(order_vars[(pi, pj)])),
                            start[pi] >= end[pj] + travel[(lj, li)]))

    # Objectives
    num_met = Sum([If(attend[p], 1, 0) for p in persons])
    total_duration = Sum([end[p] - start[p] for p in persons])

    # Latest end time among all, to minimize as tertiary objective
    end_latest = Int("latest_end")
    opt.add(end_latest >= 0)
    for p in persons:
        opt.add(end_latest >= end[p])

    h1 = opt.maximize(num_met)
    h2 = opt.maximize(total_duration)
    h3 = opt.minimize(end_latest)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary in chronological order for attended meetings
    meetings = []
    for p in persons:
        if is_true(model.eval(attend[p])):
            st = model.eval(start[p]).as_long()
            en = model.eval(end[p]).as_long()
            meetings.append({
                "person": p,
                "location": people[p]["location"],
                "start": st,
                "end": en
            })

    meetings.sort(key=lambda x: x["start"])

    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": fmt_time(m["start"]),
            "end_time": fmt_time(m["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()