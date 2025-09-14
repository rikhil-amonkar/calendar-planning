import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def solve():
    # Locations
    FD = "Financial District"
    FW = "Fisherman's Wharf"
    PH = "Pacific Heights"
    MD = "Mission District"

    # Start info
    start_location = FD
    start_time = minutes(9, 0)

    # Travel times in minutes (directed)
    travel = {
        FD: {FW: 10, PH: 13, MD: 17},
        FW: {FD: 11, PH: 12, MD: 22},
        PH: {FD: 13, FW: 13, MD: 15},
        MD: {FD: 17, FW: 22, PH: 16},
    }

    # People, locations, availabilities, and minimum meeting durations
    people = {
        "David": {
            "location": FW,
            "avail_start": minutes(10, 45),
            "avail_end": minutes(15, 30),
            "min_duration": 15,
        },
        "Timothy": {
            "location": PH,
            "avail_start": minutes(9, 0),
            "avail_end": minutes(15, 30),
            "min_duration": 75,
        },
        "Robert": {
            "location": MD,
            "avail_start": minutes(12, 15),
            "avail_end": minutes(19, 45),
            "min_duration": 90,
        },
    }

    persons = list(people.keys())

    # Z3 setup
    opt = Optimize()

    # Variables per person
    meet = {p: Bool(f"meet_{p}") for p in persons}
    s = {p: Int(f"start_{p}") for p in persons}
    e = {p: Int(f"end_{p}") for p in persons}

    # Time bounds
    for p in persons:
        opt.add(s[p] >= 0, s[p] <= 24 * 60)
        opt.add(e[p] >= 0, e[p] <= 24 * 60)

        # If meeting occurs, enforce availability and minimum duration
        opt.add(Implies(meet[p], And(
            s[p] >= people[p]["avail_start"],
            e[p] <= people[p]["avail_end"],
            e[p] > s[p],
            e[p] - s[p] >= people[p]["min_duration"]
        )))
        # If not meeting, pin times to 0 (to simplify objective expressions)
        opt.add(Implies(Not(meet[p]), And(s[p] == 0, e[p] == 0)))

    # Non-overlap with travel times between any two meetings that both occur
    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            pi = persons[i]
            pj = persons[j]
            li = people[pi]["location"]
            lj = people[pj]["location"]
            tij = travel[li][lj]
            tji = travel[lj][li]
            opt.add(Implies(And(meet[pi], meet[pj]),
                            Or(e[pi] + tij <= s[pj],
                               e[pj] + tji <= s[pi]])))

    # Reachability: each scheduled meeting must be reachable either from start location, or from another meeting prior to it with the appropriate travel time
    for p in persons:
        lp = people[p]["location"]
        from_start = s[p] >= start_time + travel[start_location][lp]
        from_others = []
        for q in persons:
            if q == p:
                continue
            lq = people[q]["location"]
            from_others.append(And(meet[q], e[q] + travel[lq][lp] <= s[p]))
        if from_others:
            opt.add(Implies(meet[p], Or(from_start, Or(from_others))))
        else:
            opt.add(Implies(meet[p], from_start))

    # Objectives:
    # 1) Maximize number of people met
    met_count = Sum([If(meet[p], 1, 0) for p in persons])
    opt.maximize(met_count)

    # 2) Maximize total meeting time
    total_meeting_minutes = Sum([If(meet[p], e[p] - s[p], 0) for p in persons])
    opt.maximize(total_meeting_minutes)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Build itinerary sorted by start time
    meetings = []
    for p in persons:
        if is_true(m.evaluate(meet[p])):
            start_min = m.evaluate(s[p]).as_long()
            end_min = m.evaluate(e[p]).as_long()
            meetings.append({
                "person": p,
                "location": people[p]["location"],
                "start": start_min,
                "end": end_min
            })

    meetings.sort(key=lambda x: x["start"])

    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": min_to_time(mt["start"]),
            "end_time": min_to_time(mt["end"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    solve()