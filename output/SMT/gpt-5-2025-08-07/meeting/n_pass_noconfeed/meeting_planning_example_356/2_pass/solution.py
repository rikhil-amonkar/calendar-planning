# SOLUTION:
# Program: Optimal meeting scheduler using Z3 SMT solver
# It computes an itinerary maximizing number of friends met and, secondarily, total meeting time,
# while respecting availability windows, travel times, and start location/time.

import json
from z3 import Int, Bool, Optimize, If, Or, And, Implies, Sum, is_true, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    BAYVIEW = "Bayview"
    NORTH_BEACH = "North Beach"
    PRESIDIO = "Presidio"
    HAIGHT = "Haight-Ashbury"
    UNION_SQUARE = "Union Square"

    # Travel times (directed, in minutes)
    travel = {
        (BAYVIEW, NORTH_BEACH): 21,
        (BAYVIEW, PRESIDIO): 31,
        (BAYVIEW, HAIGHT): 19,
        (BAYVIEW, UNION_SQUARE): 17,

        (NORTH_BEACH, BAYVIEW): 22,
        (NORTH_BEACH, PRESIDIO): 17,
        (NORTH_BEACH, HAIGHT): 18,
        (NORTH_BEACH, UNION_SQUARE): 7,

        (PRESIDIO, BAYVIEW): 31,
        (PRESIDIO, NORTH_BEACH): 18,
        (PRESIDIO, HAIGHT): 15,
        (PRESIDIO, UNION_SQUARE): 22,

        (HAIGHT, BAYVIEW): 18,
        (HAIGHT, NORTH_BEACH): 19,
        (HAIGHT, PRESIDIO): 15,
        (HAIGHT, UNION_SQUARE): 17,

        (UNION_SQUARE, BAYVIEW): 15,
        (UNION_SQUARE, NORTH_BEACH): 10,
        (UNION_SQUARE, PRESIDIO): 24,
        (UNION_SQUARE, HAIGHT): 18,
    }

    def t(a, b):
        return travel[(a, b)]

    # Start at Bayview at 9:00
    day_start_loc = BAYVIEW
    day_start_time = minutes(9, 0)
    day_end_time = 24 * 60

    # Friends and constraints
    friends = [
        {
            "person": "Barbara",
            "location": NORTH_BEACH,
            "window_start": minutes(13, 45),
            "window_end": minutes(20, 15),
            "min_duration": 60
        },
        {
            "person": "Margaret",
            "location": PRESIDIO,
            "window_start": minutes(10, 15),
            "window_end": minutes(15, 15),
            "min_duration": 30
        },
        {
            "person": "Kevin",
            "location": HAIGHT,
            "window_start": minutes(20, 0),
            "window_end": minutes(20, 45),
            "min_duration": 30
        },
        {
            "person": "Kimberly",
            "location": UNION_SQUARE,
            "window_start": minutes(7, 45),
            "window_end": minutes(16, 45),
            "min_duration": 30
        },
    ]

    o = Optimize()
    o.set('priority', 'lex')

    # Create variables for each meeting
    vars_by_person = {}
    for fr in friends:
        name = fr["person"]
        si = Int(f"start_{name}")
        ei = Int(f"end_{name}")
        di = Int(f"dur_{name}")
        sel = Bool(f"sel_{name}")

        # Bounds for selected meetings
        o.add(Implies(sel, And(
            si >= fr["window_start"],
            ei <= fr["window_end"],
            di >= fr["min_duration"],
            di == ei - si
        )))
        # Must be reachable from starting point at 9:00 from Bayview
        o.add(Implies(sel, si >= day_start_time + t(day_start_loc, fr["location"])))

        # For non-selected, set zero duration and aligned times (within 0..day_end_time)
        o.add(Implies(~sel, And(
            di == 0,
            si >= 0, si <= day_end_time,
            ei == si
        )))

        # Universal bounds to keep within day
        o.add(si >= 0, si <= day_end_time)
        o.add(ei >= 0, ei <= day_end_time)
        o.add(di >= 0)

        vars_by_person[name] = {
            "start": si,
            "end": ei,
            "dur": di,
            "sel": sel,
            "location": fr["location"],
            "window_start": fr["window_start"],
            "window_end": fr["window_end"],
            "min_duration": fr["min_duration"],
        }

    # Pairwise travel/order constraints for all selected pairs
    names = [fr["person"] for fr in friends]
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a = names[i]
            b = names[j]
            va = vars_by_person[a]
            vb = vars_by_person[b]
            # If both selected, enforce that either a before b with travel or b before a with travel
            o.add(Implies(And(va["sel"], vb["sel"]),
                          Or(
                              va["end"] + t(va["location"], vb["location"]) <= vb["start"],
                              vb["end"] + t(vb["location"], va["location"]) <= va["start"]
                          )))

    # Objectives
    total_meetings = Sum([If(vars_by_person[n]["sel"], 1, 0) for n in names])
    total_duration = Sum([vars_by_person[n]["dur"] for n in names])

    o.maximize(total_meetings)
    o.maximize(total_duration)

    # Correct satisfiability check
    if o.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = o.model()

    # Build itinerary from selected meetings, sorted by start time
    events = []
    for fr in friends:
        name = fr["person"]
        v = vars_by_person[name]
        if is_true(m.evaluate(v["sel"])):
            s = m.evaluate(v["start"]).as_long()
            e = m.evaluate(v["end"]).as_long()
            events.append({
                "person": name,
                "location": v["location"],
                "start": s,
                "end": e
            })

    events.sort(key=lambda x: x["start"])

    itinerary = []
    for ev in events:
        itinerary.append({
            "action": "meet",
            "location": ev["location"],
            "person": ev["person"],
            "start_time": fmt_time(ev["start"]),
            "end_time": fmt_time(ev["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()