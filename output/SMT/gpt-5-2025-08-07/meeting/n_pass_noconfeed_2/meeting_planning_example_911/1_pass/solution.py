import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Time horizon
    START_DAY = 9 * 60  # 9:00 -> 540
    END_DAY = 21 * 60   # 21:00 -> 1260

    # Locations
    locs = [
        "The Castro", "North Beach", "Golden Gate Park", "Embarcadero",
        "Haight-Ashbury", "Richmond District", "Nob Hill", "Marina District",
        "Presidio", "Union Square", "Financial District"
    ]

    # Travel times (minutes)
    T = {
        "The Castro": {
            "North Beach": 20, "Golden Gate Park": 11, "Embarcadero": 22, "Haight-Ashbury": 6,
            "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Presidio": 20,
            "Union Square": 19, "Financial District": 21
        },
        "North Beach": {
            "The Castro": 23, "Golden Gate Park": 22, "Embarcadero": 6, "Haight-Ashbury": 18,
            "Richmond District": 18, "Nob Hill": 7, "Marina District": 9, "Presidio": 17,
            "Union Square": 7, "Financial District": 8
        },
        "Golden Gate Park": {
            "The Castro": 13, "North Beach": 23, "Embarcadero": 25, "Haight-Ashbury": 7,
            "Richmond District": 7, "Nob Hill": 20, "Marina District": 16, "Presidio": 11,
            "Union Square": 22, "Financial District": 26
        },
        "Embarcadero": {
            "The Castro": 25, "North Beach": 5, "Golden Gate Park": 25, "Haight-Ashbury": 21,
            "Richmond District": 21, "Nob Hill": 10, "Marina District": 12, "Presidio": 20,
            "Union Square": 10, "Financial District": 5
        },
        "Haight-Ashbury": {
            "The Castro": 6, "North Beach": 19, "Golden Gate Park": 7, "Embarcadero": 20,
            "Richmond District": 10, "Nob Hill": 15, "Marina District": 17, "Presidio": 15,
            "Union Square": 19, "Financial District": 21
        },
        "Richmond District": {
            "The Castro": 16, "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
            "Haight-Ashbury": 10, "Nob Hill": 17, "Marina District": 9, "Presidio": 7,
            "Union Square": 21, "Financial District": 22
        },
        "Nob Hill": {
            "The Castro": 17, "North Beach": 8, "Golden Gate Park": 17, "Embarcadero": 9,
            "Haight-Ashbury": 13, "Richmond District": 14, "Marina District": 11, "Presidio": 17,
            "Union Square": 7, "Financial District": 9
        },
        "Marina District": {
            "The Castro": 22, "North Beach": 11, "Golden Gate Park": 18, "Embarcadero": 14,
            "Haight-Ashbury": 16, "Richmond District": 11, "Nob Hill": 12, "Presidio": 10,
            "Union Square": 16, "Financial District": 17
        },
        "Presidio": {
            "The Castro": 21, "North Beach": 18, "Golden Gate Park": 12, "Embarcadero": 20,
            "Haight-Ashbury": 15, "Richmond District": 7, "Nob Hill": 18, "Marina District": 11,
            "Union Square": 22, "Financial District": 23
        },
        "Union Square": {
            "The Castro": 17, "North Beach": 10, "Golden Gate Park": 22, "Embarcadero": 11,
            "Haight-Ashbury": 18, "Richmond District": 20, "Nob Hill": 9, "Marina District": 18,
            "Presidio": 24, "Financial District": 9
        },
        "Financial District": {
            "The Castro": 20, "North Beach": 7, "Golden Gate Park": 23, "Embarcadero": 4,
            "Haight-Ashbury": 19, "Richmond District": 21, "Nob Hill": 8, "Marina District": 15,
            "Presidio": 22, "Union Square": 9
        }
    }
    # Ensure self-travel is zero
    for a in locs:
        if a not in T:
            T[a] = {}
        T[a][a] = 0

    def travel(a, b):
        return T[a][b]

    # People, locations, availability windows (in minutes), and minimum meet durations
    people = [
        dict(person="Steven", location="North Beach", start=17*60+30, end=20*60+30, min_dur=15),
        dict(person="Sarah", location="Golden Gate Park", start=17*60, end=19*60+15, min_dur=75),
        dict(person="Brian", location="Embarcadero", start=14*60+15, end=16*60, min_dur=105),
        dict(person="Stephanie", location="Haight-Ashbury", start=10*60+15, end=12*60+15, min_dur=75),
        dict(person="Melissa", location="Richmond District", start=14*60, end=19*60+30, min_dur=30),
        dict(person="Nancy", location="Nob Hill", start=8*60+15, end=12*60+45, min_dur=90),
        dict(person="David", location="Marina District", start=11*60+15, end=13*60+15, min_dur=120),
        dict(person="James", location="Presidio", start=15*60, end=18*60+15, min_dur=120),
        dict(person="Elizabeth", location="Union Square", start=11*60+30, end=21*60, min_dur=60),
        dict(person="Robert", location="Financial District", start=13*60+15, end=15*60+15, min_dur=45),
    ]

    n = len(people)
    names = [p["person"] for p in people]

    # Z3 variables
    meet = {p["person"]: Bool(f"meet_{p['person']}") for p in people}
    s = {p["person"]: Int(f"s_{p['person']}") for p in people}
    e = {p["person"]: Int(f"e_{p['person']}") for p in people}

    # Pairwise order variables
    order = {}
    for i in range(n):
        for j in range(i+1, n):
            key = (people[i]["person"], people[j]["person"])
            order[key] = Bool(f"order_{people[i]['person']}_before_{people[j]['person']}")

    opt = Optimize()

    # Constraints per person
    for p in people:
        name = p["person"]
        loc = p["location"]
        avail_start = p["start"]
        avail_end = p["end"]
        min_dur = p["min_dur"]

        # If meeting, start within availability and horizon, fixed duration = min_dur
        opt.add(Implies(meet[name], And(
            s[name] >= avail_start,
            s[name] >= START_DAY + travel("The Castro", loc),
            e[name] == s[name] + min_dur,
            e[name] <= avail_end,
            s[name] >= START_DAY,
            e[name] <= END_DAY
        )))
        # If not meeting, set times to 0
        opt.add(Implies(Not(meet[name]), And(s[name] == 0, e[name] == 0)))

    # Disjunctive travel-time constraints between meetings
    for i in range(n):
        for j in range(i+1, n):
            pi = people[i]
            pj = people[j]
            ni, nj = pi["person"], pj["person"]
            li, lj = pi["location"], pj["location"]
            tij = travel(li, lj)
            tji = travel(lj, li)
            oij = order[(ni, nj)]
            # If both meetings occur and i before j
            opt.add(Implies(And(meet[ni], meet[nj], oij), s[nj] >= e[ni] + tij))
            # If both meetings occur and j before i
            opt.add(Implies(And(meet[ni], meet[nj], Not(oij)), s[ni] >= e[nj] + tji))

    # Objective: maximize number of meetings
    total_meetings = Sum([If(meet[p["person"]], 1, 0) for p in people])
    opt.maximize(total_meetings)

    # Secondary (tie-breaker): minimize latest end time among held meetings
    latest_end = Int("latest_end")
    opt.add(latest_end >= START_DAY)
    for p in people:
        name = p["person"]
        opt.add(Implies(meet[name], latest_end >= e[name]))
    opt.minimize(latest_end)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Build itinerary
    itinerary = []
    for p in people:
        name = p["person"]
        loc = p["location"]
        if is_true(m[meet[name]]):
            start = m[s[name]].as_long()
            end = m[e[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_str(start),
                "end_time": minutes_to_str(end)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()