# Z3-based scheduler for meeting friends in San Francisco
# Objective: maximize the number of friends met while respecting travel times and availability windows.

from z3 import Optimize, Int, Bool, And, Or, If, Sum
import json

def minutes_since(day_start_h, day_start_m, h, m):
    return (h - day_start_h) * 60 + (m - day_start_m)

def to_time_str(day_start_h, day_start_m, mins_from_start):
    total_minutes = day_start_h * 60 + day_start_m + int(mins_from_start)
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

def solve_itinerary():
    # Day starts at 09:00 at Union Square
    DAY_START_H, DAY_START_M = 9, 0
    start_location = "Union Square"

    # Travel times (directed, minutes)
    travel = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Sunset District"): 26,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Sunset District"): 23,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Bayview"): 22,
    }

    # People data: name -> dict with location, availability window (start, end) in minutes since 09:00, and min duration
    people = {
        "Rebecca": {
            "location": "Mission District",
            "avail_start": minutes_since(DAY_START_H, DAY_START_M, 11, 30),
            "avail_end": minutes_since(DAY_START_H, DAY_START_M, 20, 15),
            "min_dur": 120,
        },
        "Karen": {
            "location": "Bayview",
            "avail_start": minutes_since(DAY_START_H, DAY_START_M, 12, 45),
            "avail_end": minutes_since(DAY_START_H, DAY_START_M, 15, 0),
            "min_dur": 120,
        },
        "Carol": {
            "location": "Sunset District",
            "avail_start": minutes_since(DAY_START_H, DAY_START_M, 10, 15),
            "avail_end": minutes_since(DAY_START_H, DAY_START_M, 11, 45),
            "min_dur": 30,
        },
    }

    persons = list(people.keys())
    opt = Optimize()

    start_vars = {}
    end_vars = {}
    meet_vars = {}

    # Create variables and constraints
    for p in persons:
        s = Int(f"{p}_start")
        e = Int(f"{p}_end")
        m = Bool(f"{p}_meet")
        start_vars[p] = s
        end_vars[p] = e
        meet_vars[p] = m

        # Variable domains
        opt.add(If(m, And(s >= 0, e >= 0), And(s == 0, e == 0)))

        # Availability and duration constraints if meeting
        avail_start = people[p]["avail_start"]
        avail_end = people[p]["avail_end"]
        min_dur = people[p]["min_dur"]

        opt.add(Or(
            m == False,
            And(
                s >= avail_start,
                e <= avail_end,
                e - s >= min_dur
            )
        ))

        # Reachability from starting location by 09:00 (safe for earliest meeting)
        loc = people[p]["location"]
        t0 = travel[(start_location, loc)]
        opt.add(Or(m == False, s >= t0))

    # Non-overlap and travel time constraints between meetings
    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            p, q = persons[i], persons[j]
            lp, lq = people[p]["location"], people[q]["location"]
            tpq = travel[(lp, lq)]
            tqp = travel[(lq, lp)]
            sp, ep, mp = start_vars[p], end_vars[p], meet_vars[p]
            sq, eq, mq = start_vars[q], end_vars[q], meet_vars[q]

            # If meeting both, then one must follow the other with enough travel time
            opt.add(Or(
                mp == False, mq == False,
                Or(ep + tpq <= sq, eq + tqp <= sp)
            ))

    # Objective: maximize the number of friends met
    total_meetings = Sum([If(meet_vars[p], 1, 0) for p in persons])
    opt.maximize(total_meetings)

    # Tie-breakers: prefer earlier schedule (minimize total end times and start times)
    opt.minimize(Sum([end_vars[p] for p in persons]))
    opt.minimize(Sum([start_vars[p] for p in persons]))

    if opt.check() != sat:
        return {"itinerary": []}

    model = opt.model()

    # Build itinerary
    meetings = []
    for p in persons:
        if model.eval(meet_vars[p], model_completion=True):
            s = model.eval(start_vars[p], model_completion=True).as_long()
            e = model.eval(end_vars[p], model_completion=True).as_long()
            meetings.append({
                "action": "meet",
                "person": p,
                "start": s,
                "end": e
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Convert to required format with HH:MM 24-hour times
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": to_time_str(DAY_START_H, DAY_START_M, m["start"]),
            "end_time": to_time_str(DAY_START_H, DAY_START_M, m["end"])
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))