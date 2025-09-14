import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations and asymmetric travel times (in minutes)
    locations = [
        "Embarcadero",
        "Richmond District",
        "Union Square",
        "Financial District",
        "Pacific Heights",
        "Nob Hill",
        "Bayview",
    ]

    travel = {
        "Embarcadero": {
            "Embarcadero": 0,
            "Richmond District": 21,
            "Union Square": 10,
            "Financial District": 5,
            "Pacific Heights": 11,
            "Nob Hill": 10,
            "Bayview": 21,
        },
        "Richmond District": {
            "Embarcadero": 19,
            "Richmond District": 0,
            "Union Square": 21,
            "Financial District": 22,
            "Pacific Heights": 10,
            "Nob Hill": 17,
            "Bayview": 26,
        },
        "Union Square": {
            "Embarcadero": 11,
            "Richmond District": 20,
            "Union Square": 0,
            "Financial District": 9,
            "Pacific Heights": 15,
            "Nob Hill": 9,
            "Bayview": 15,
        },
        "Financial District": {
            "Embarcadero": 4,
            "Richmond District": 21,
            "Union Square": 9,
            "Financial District": 0,
            "Pacific Heights": 13,
            "Nob Hill": 8,
            "Bayview": 19,
        },
        "Pacific Heights": {
            "Embarcadero": 10,
            "Richmond District": 12,
            "Union Square": 12,
            "Financial District": 13,
            "Nob Hill": 8,
            "Bayview": 22,
        },
        "Nob Hill": {
            "Embarcadero": 9,
            "Richmond District": 14,
            "Union Square": 7,
            "Financial District": 9,
            "Pacific Heights": 8,
            "Bayview": 19,
        },
        "Bayview": {
            "Embarcadero": 19,
            "Richmond District": 25,
            "Union Square": 17,
            "Financial District": 19,
            "Pacific Heights": 23,
            "Nob Hill": 20,
            "Bayview": 0,
        },
    }

    # People, locations, availability windows, and minimum meeting durations
    # Times in minutes from 0:00
    # You arrive at Embarcadero at 9:00 (540)
    people = [
        {
            "name": "Kenneth",
            "location": "Richmond District",
            "avail_start": 21 * 60 + 15,  # 21:15
            "avail_end": 22 * 60,         # 22:00
            "min_dur": 30,
        },
        {
            "name": "Lisa",
            "location": "Union Square",
            "avail_start": 9 * 60,        # 9:00
            "avail_end": 16 * 60 + 30,    # 16:30
            "min_dur": 45,
        },
        {
            "name": "Joshua",
            "location": "Financial District",
            "avail_start": 12 * 60,       # 12:00
            "avail_end": 15 * 60 + 15,    # 15:15
            "min_dur": 15,
        },
        {
            "name": "Nancy",
            "location": "Pacific Heights",
            "avail_start": 8 * 60,        # 8:00
            "avail_end": 11 * 60 + 30,    # 11:30
            "min_dur": 90,
        },
        {
            "name": "Andrew",
            "location": "Nob Hill",
            "avail_start": 11 * 60 + 30,  # 11:30
            "avail_end": 20 * 60 + 15,    # 20:15
            "min_dur": 60,
        },
        {
            "name": "John",
            "location": "Bayview",
            "avail_start": 16 * 60 + 45,  # 16:45
            "avail_end": 21 * 60 + 30,    # 21:30
            "min_dur": 75,
        },
    ]

    start_location = "Embarcadero"
    start_time = 9 * 60  # 9:00

    n = len(people)

    # Z3 variables
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    meet_vars = [Bool(f"meet_{i}") for i in range(n)]

    opt = Optimize()

    # Domain constraints and per-person constraints
    for i, p in enumerate(people):
        s, e, m = s_vars[i], e_vars[i], meet_vars[i]
        a_s, a_e, dmin = p["avail_start"], p["avail_end"], p["min_dur"]

        # Bound times in reasonable day range
        opt.add(And(s >= 0, s <= 24 * 60, e >= 0, e <= 24 * 60))

        # If meeting, enforce within availability and duration
        opt.add(Implies(m, And(s >= a_s, e <= a_e, e - s >= dmin, e >= s)))
        # If not meeting, pin to 0 to avoid spurious values
        opt.add(Implies(Not(m), And(s == 0, e == 0)))

    # Travel separation constraints between meetings
    for i in range(n):
        for j in range(i + 1, n):
            li = people[i]["location"]
            lj = people[j]["location"]
            tij = travel[li][lj]
            tji = travel[lj][li]
            opt.add(
                Implies(
                    And(meet_vars[i], meet_vars[j]),
                    Or(
                        s_vars[i] >= e_vars[j] + tji,  # i after j
                        s_vars[j] >= e_vars[i] + tij   # j after i
                    )
                )
            )

    # Reachability constraint from start or from another met meeting
    for i in range(n):
        li = people[i]["location"]
        from_start = s_vars[i] >= start_time + travel[start_location][li]
        preds = []
        for j in range(n):
            if j == i:
                continue
            lj = people[j]["location"]
            preds.append(And(meet_vars[j], e_vars[j] + travel[lj][li] <= s_vars[i]))
        # If i is met, then either it's reachable from start or from at least one earlier meeting
        opt.add(Implies(meet_vars[i], Or(from_start, Or(preds) if preds else from_start)))

    # Objective: maximize number of friends met
    count = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(count)

    # Secondary: maximize total meeting time
    total_meeting_time = Sum([If(meet_vars[i], e_vars[i] - s_vars[i], 0) for i in range(n)])
    opt.maximize(total_meeting_time)

    # Tertiary: minimize latest end time (tie-breaker)
    L = Int("latest_end")
    opt.add(L >= 0)
    for i in range(n):
        opt.add(L >= e_vars[i])
    opt.minimize(L)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract meetings
    meetings = []
    for i, p in enumerate(people):
        if is_true(model.eval(meet_vars[i])):
            s = model.eval(s_vars[i]).as_long()
            e = model.eval(e_vars[i]).as_long()
            meetings.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": s,
                "end": e
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Format times
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": minutes_to_str(m["start"]),
            "end_time": minutes_to_str(m["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()