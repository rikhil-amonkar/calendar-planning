# SOLUTION:
import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    FD = "Financial District"
    CH = "Chinatown"
    AS = "Alamo Square"
    BV = "Bayview"
    FW = "Fisherman's Wharf"

    locations = [FD, CH, AS, BV, FW]

    # Travel times (in minutes), directed
    travel = {
        FD: {CH: 5,  AS: 17, BV: 19, FW: 10},
        CH: {FD: 5,  AS: 17, BV: 22, FW: 8},
        AS: {FD: 17, CH: 16, BV: 16, FW: 19},
        BV: {FD: 19, CH: 18, AS: 16, FW: 25},
        FW: {FD: 11, CH: 12, AS: 20, BV: 26},
    }

    def travel_time(a, b):
        if a == b:
            return 0
        return travel[a][b]

    # Start info
    start_location = FD
    start_time = minutes(9, 0)

    # People and constraints
    people = {
        "Nancy":   {"location": CH, "avail_start": minutes(9, 30),  "avail_end": minutes(13, 30), "min_meet": 90},
        "Mary":    {"location": AS, "avail_start": minutes(7, 0),   "avail_end": minutes(21, 0),  "min_meet": 75},
        "Jessica": {"location": BV, "avail_start": minutes(11, 15), "avail_end": minutes(13, 45), "min_meet": 45},
        "Rebecca": {"location": FW, "avail_start": minutes(7, 0),   "avail_end": minutes(8, 30),  "min_meet": 45},
    }

    names = list(people.keys())

    o = Optimize()
    o.set(priority='lex')

    # Variables
    meet = {n: Bool(f"meet_{n}") for n in names}
    start = {n: Int(f"start_{n}") for n in names}
    end = {n: Int(f"end_{n}") for n in names}
    first = {n: Bool(f"first_{n}") for n in names}

    # Bounds and availability constraints
    for n in names:
        loc = people[n]["location"]
        a_s = people[n]["avail_start"]
        a_e = people[n]["avail_end"]
        min_dur = people[n]["min_meet"]

        # Time bounds
        o.add(start[n] >= 0, start[n] <= 24*60)
        o.add(end[n] >= 0, end[n] <= 24*60)

        # If meeting occurs, enforce availability and duration
        o.add(Implies(meet[n], And(start[n] >= a_s,
                                   end[n] <= a_e,
                                   end[n] - start[n] >= min_dur)))
        # If not meeting, keep start=end (zero interval, unused)
        o.add(Implies(Not(meet[n]), end[n] == start[n]))

        # First implies meet
        o.add(Implies(first[n], meet[n]))

        # If this person is the first meeting, must be reachable from origin
        o.add(Implies(first[n], start[n] >= start_time + travel_time(start_location, loc)))

    # Exactly one "first" if we meet anyone; else none
    has_meet = Bool("has_meet")
    o.add(has_meet == Or([meet[n] for n in names]))
    sum_first = Sum([If(first[n], 1, 0) for n in names])
    o.add(sum_first == If(has_meet, 1, 0))

    # If i is first, it must be before all other meetings
    for i in names:
        for j in names:
            if i == j:
                continue
            # If i is first and j is met, j must start after i ends plus travel
            o.add(Implies(And(first[i], meet[j]),
                          start[j] >= end[i] + travel_time(people[i]["location"], people[j]["location"])))

    # Non-overlap and travel-time feasibility between any pair met
    for i_idx in range(len(names)):
        for j_idx in range(i_idx + 1, len(names)):
            i = names[i_idx]
            j = names[j_idx]
            li = people[i]["location"]
            lj = people[j]["location"]
            o.add(Implies(And(meet[i], meet[j]),
                          Or(end[i] + travel_time(li, lj) <= start[j],
                             end[j] + travel_time(lj, li) <= start[i])))

    # Objectives:
    total_met = Sum([If(meet[n], 1, 0) for n in names])
    # Last end time among meetings
    last_end = Max([If(meet[n], end[n], 0) for n in names])
    # Total meeting minutes (for tie-breaking after earlier finish)
    total_minutes = Sum([If(meet[n], end[n] - start[n], 0) for n in names])

    o.maximize(total_met)
    o.minimize(last_end)
    o.maximize(total_minutes)

    if o.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = o.model()

    meetings = []
    for n in names:
        if is_true(m.evaluate(meet[n], model_completion=True)):
            s = m.evaluate(start[n], model_completion=True).as_long()
            e = m.evaluate(end[n], model_completion=True).as_long()
            meetings.append({
                "action": "meet",
                "location": people[n]["location"],
                "person": n,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    # Sort itinerary by start time
    meetings.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    result = {
        "itinerary": meetings
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()