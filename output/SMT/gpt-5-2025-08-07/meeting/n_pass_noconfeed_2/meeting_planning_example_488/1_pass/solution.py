import json
from z3 import *

def minutes(h, m):
    return h*60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    locations = [
        "Pacific Heights",
        "Nob Hill",
        "Russian Hill",
        "The Castro",
        "Sunset District",
        "Haight-Ashbury",
    ]

    start_location = "Pacific Heights"
    arrival_time = minutes(9, 0)  # 9:00

    # Directed travel times (in minutes)
    t = {
        "Pacific Heights": {
            "Nob Hill": 8,
            "Russian Hill": 7,
            "The Castro": 16,
            "Sunset District": 21,
            "Haight-Ashbury": 11,
        },
        "Nob Hill": {
            "Pacific Heights": 8,
            "Russian Hill": 5,
            "The Castro": 17,
            "Sunset District": 25,
            "Haight-Ashbury": 13,
        },
        "Russian Hill": {
            "Pacific Heights": 7,
            "Nob Hill": 5,
            "The Castro": 21,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
        },
        "The Castro": {
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Russian Hill": 18,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
        },
        "Sunset District": {
            "Pacific Heights": 21,
            "Nob Hill": 27,
            "Russian Hill": 24,
            "The Castro": 17,
            "Haight-Ashbury": 15,
        },
        "Haight-Ashbury": {
            "Pacific Heights": 12,
            "Nob Hill": 15,
            "Russian Hill": 17,
            "The Castro": 6,
            "Sunset District": 15,
        },
    }

    # Ensure self-travel is 0
    for a in locations:
        if a not in t:
            t[a] = {}
        t[a][a] = 0

    # Participants: name -> dict with location, window_start, window_end, min_duration
    friends = {
        "Ronald": {
            "location": "Nob Hill",
            "window_start": minutes(10, 0),
            "window_end": minutes(17, 0),
            "min_duration": 105,
        },
        "Sarah": {
            "location": "Russian Hill",
            "window_start": minutes(7, 15),
            "window_end": minutes(9, 30),
            "min_duration": 45,
        },
        "Helen": {
            "location": "The Castro",
            "window_start": minutes(13, 30),
            "window_end": minutes(17, 0),
            "min_duration": 120,
        },
        "Joshua": {
            "location": "Sunset District",
            "window_start": minutes(14, 15),
            "window_end": minutes(19, 30),
            "min_duration": 90,
        },
        "Margaret": {
            "location": "Haight-Ashbury",
            "window_start": minutes(10, 15),
            "window_end": minutes(22, 0),
            "min_duration": 60,
        },
    }

    people = list(friends.keys())
    n = len(people)

    # Z3 variables
    sel = {p: Bool(f"{p}_sel") for p in people}
    start = {p: Int(f"{p}_start") for p in people}
    end = {p: Int(f"{p}_end") for p in people}
    pos = {p: Int(f"{p}_pos") for p in people}

    opt = Optimize()

    # Domains and basic constraints
    for p in people:
        w_start = friends[p]["window_start"]
        w_end = friends[p]["window_end"]
        min_dur = friends[p]["min_duration"]

        opt.add(start[p] >= 0, start[p] <= 24*60)
        opt.add(end[p] >= 0, end[p] <= 24*60)
        opt.add(end[p] >= start[p])

        # Selection implies window and min duration
        opt.add(Implies(sel[p], And(start[p] >= w_start,
                                    end[p] <= w_end,
                                    end[p] - start[p] >= min_dur)))

        # If not selected, collapse interval and pos = 0
        opt.add(Implies(Not(sel[p]), And(end[p] == start[p], pos[p] == 0)))

        # Pos domain: 0..n; if selected, 1..n
        opt.add(pos[p] >= 0, pos[p] <= n)
        opt.add(Implies(sel[p], And(pos[p] >= 1, pos[p] <= n)))

    # Unique positions among selected
    for i in range(n):
        for j in range(i+1, n):
            pi, pj = people[i], people[j]
            opt.add(Implies(And(sel[pi], sel[pj]), pos[pi] != pos[pj]))

    # Ordering and travel-time separation using positions
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            pi, pj = people[i], people[j]
            li = friends[pi]["location"]
            lj = friends[pj]["location"]
            travel_ij = t[li][lj]
            opt.add(Implies(And(sel[pi], sel[pj], pos[pi] < pos[pj]),
                            end[pi] + travel_ij <= start[pj]))

    # Anchor: first scheduled meeting (pos == 1) must be reachable from start location at arrival_time
    for p in people:
        loc = friends[p]["location"]
        travel_from_start = t[start_location][loc]
        opt.add(Implies(And(sel[p], pos[p] == 1),
                        start[p] >= arrival_time + travel_from_start))

    # Ensure exactly one "first" if any selected
    first_flags = [If(And(sel[p], pos[p] == 1), 1, 0) for p in people]
    sum_sel = Sum([If(sel[p], 1, 0) for p in people])
    opt.add(Sum(first_flags) == If(sum_sel == 0, 0, 1))

    # Secondary objective: minimize last end time to prefer earlier finish
    last_end = Int("last_end")
    opt.add(last_end >= arrival_time)
    for p in people:
        opt.add(last_end >= end[p])

    # Objectives
    h1 = opt.maximize(sum_sel)
    h2 = opt.minimize(last_end)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Build itinerary, ordered by position
    selected_entries = []
    for p in people:
        if m.evaluate(sel[p], model_completion=True):
            p_pos = m.evaluate(pos[p], model_completion=True).as_long()
            s = m.evaluate(start[p], model_completion=True).as_long()
            e = m.evaluate(end[p], model_completion=True).as_long()
            selected_entries.append((p_pos, {
                "action": "meet",
                "location": friends[p]["location"],
                "person": p,
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e),
            }))

    selected_entries.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in selected_entries]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()