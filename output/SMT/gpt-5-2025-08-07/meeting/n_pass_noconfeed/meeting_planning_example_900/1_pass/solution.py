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
    RD = "Richmond District"
    CASTRO = "The Castro"
    NOB = "Nob Hill"
    MARINA = "Marina District"
    PACIFIC = "Pacific Heights"
    HAIGHT = "Haight-Ashbury"
    MISSION = "Mission District"
    CHINA = "Chinatown"
    RUSSIAN = "Russian Hill"
    ALAMO = "Alamo Square"
    BAYVIEW = "Bayview"

    # Directed travel times (minutes)
    dist = {
        RD: {
            CASTRO: 16, NOB: 17, MARINA: 9, PACIFIC: 10, HAIGHT: 10,
            MISSION: 20, CHINA: 20, RUSSIAN: 13, ALAMO: 13, BAYVIEW: 27
        },
        CASTRO: {
            RD: 16, NOB: 16, MARINA: 21, PACIFIC: 16, HAIGHT: 6,
            MISSION: 7, CHINA: 22, RUSSIAN: 18, ALAMO: 8, BAYVIEW: 19
        },
        NOB: {
            RD: 14, CASTRO: 17, MARINA: 11, PACIFIC: 8, HAIGHT: 13,
            MISSION: 13, CHINA: 6, RUSSIAN: 5, ALAMO: 11, BAYVIEW: 19
        },
        MARINA: {
            RD: 11, CASTRO: 22, NOB: 12, PACIFIC: 7, HAIGHT: 16,
            MISSION: 20, CHINA: 15, RUSSIAN: 8, ALAMO: 15, BAYVIEW: 27
        },
        PACIFIC: {
            RD: 12, CASTRO: 16, NOB: 8, MARINA: 6, HAIGHT: 11,
            MISSION: 15, CHINA: 11, RUSSIAN: 7, ALAMO: 10, BAYVIEW: 22
        },
        HAIGHT: {
            RD: 10, CASTRO: 6, NOB: 15, MARINA: 17, PACIFIC: 12,
            MISSION: 11, CHINA: 19, RUSSIAN: 17, ALAMO: 5, BAYVIEW: 18
        },
        MISSION: {
            RD: 20, CASTRO: 7, NOB: 12, MARINA: 19, PACIFIC: 16,
            HAIGHT: 12, CHINA: 16, RUSSIAN: 15, ALAMO: 11, BAYVIEW: 14
        },
        CHINA: {
            RD: 20, CASTRO: 22, NOB: 9, MARINA: 12, PACIFIC: 10,
            HAIGHT: 19, MISSION: 17, RUSSIAN: 7, ALAMO: 17, BAYVIEW: 20
        },
        RUSSIAN: {
            RD: 14, CASTRO: 21, NOB: 5, MARINA: 7, PACIFIC: 7,
            HAIGHT: 17, MISSION: 16, CHINA: 9, ALAMO: 15, BAYVIEW: 23
        },
        ALAMO: {
            RD: 11, CASTRO: 8, NOB: 11, MARINA: 15, PACIFIC: 10,
            HAIGHT: 5, MISSION: 10, CHINA: 15, RUSSIAN: 13, BAYVIEW: 16
        },
        BAYVIEW: {
            RD: 25, CASTRO: 19, NOB: 20, MARINA: 27, PACIFIC: 23,
            HAIGHT: 19, MISSION: 13, CHINA: 19, RUSSIAN: 23, ALAMO: 16
        }
    }

    # People and constraints
    people = [
        {"name": "Matthew",   "location": CASTRO,  "start": minutes(16,30), "end": minutes(20,0),  "min_dur": 45},
        {"name": "Rebecca",   "location": NOB,     "start": minutes(15,15), "end": minutes(19,15), "min_dur": 105},
        {"name": "Brian",     "location": MARINA,  "start": minutes(14,15), "end": minutes(22,0),  "min_dur": 30},
        {"name": "Emily",     "location": PACIFIC, "start": minutes(11,15), "end": minutes(19,45), "min_dur": 15},
        {"name": "Karen",     "location": HAIGHT,  "start": minutes(11,45), "end": minutes(17,30), "min_dur": 30},
        {"name": "Stephanie", "location": MISSION, "start": minutes(13,0),  "end": minutes(15,45), "min_dur": 75},
        {"name": "James",     "location": CHINA,   "start": minutes(14,30), "end": minutes(19,0),  "min_dur": 120},
        {"name": "Steven",    "location": RUSSIAN, "start": minutes(14,0),  "end": minutes(20,0),  "min_dur": 30},
        {"name": "Elizabeth", "location": ALAMO,   "start": minutes(13,0),  "end": minutes(17,15), "min_dur": 120},
        {"name": "William",   "location": BAYVIEW, "start": minutes(18,15), "end": minutes(20,15), "min_dur": 90},
    ]

    # Z3 variables
    s = {p["name"]: Int(f"s_{p['name']}") for p in people}
    e = {p["name"]: Int(f"e_{p['name']}") for p in people}
    a = {p["name"]: Bool(f"a_{p['name']}") for p in people}

    opt = Optimize()
    opt.set("priority", "lex")

    # Basic constraints for each person if attended
    for p in people:
        pn = p["name"]
        opt.add(Implies(a[pn], And(
            s[pn] >= p["start"],
            e[pn] <= p["end"],
            e[pn] - s[pn] >= p["min_dur"],
            s[pn] >= 0, e[pn] >= 0,
            s[pn] <= minutes(23, 59), e[pn] <= minutes(23, 59)
        )))
        # If not attending, keep times within a broad domain to avoid model weirdness
        opt.add(Implies(Not(a[pn]), And(s[pn] >= 0, s[pn] <= minutes(23,59),
                                        e[pn] >= 0, e[pn] <= minutes(23,59))))

    # Pairwise disjunctive ordering with travel times when both attended
    for i in range(len(people)):
        for j in range(i+1, len(people)):
            pi = people[i]
            pj = people[j]
            ni = pi["name"]
            nj = pj["name"]
            li = pi["location"]
            lj = pj["location"]
            travel_ij = dist[li][lj]
            travel_ji = dist[lj][li]
            opt.add(Implies(And(a[ni], a[nj]), Or(
                e[ni] + travel_ij <= s[nj],
                e[nj] + travel_ji <= s[ni]
            )))

    # Start at Richmond District at 9:00
    start_time = minutes(9, 0)
    for p in people:
        pn = p["name"]
        loc = p["location"]
        # Either we can reach p from RD after 9:00, or (infeasible) finish p and get back to RD by 9:00
        # The second branch will be naturally ruled out by availability; this enforces the initial travel requirement.
        opt.add(Implies(a[pn], Or(
            start_time + dist[RD][loc] <= s[pn],
            e[pn] + dist[loc][RD] <= start_time
        )))

    # Objectives: maximize number of friends met, then maximize total meeting time
    sum_attended = Sum([If(a[p["name"]], 1, 0) for p in people])
    total_meeting_time = Sum([If(a[p["name"]], e[p["name"]] - s[p["name"]], 0) for p in people])

    opt.maximize(sum_attended)
    opt.maximize(total_meeting_time)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    meetings = []
    for p in people:
        pn = p["name"]
        if is_true(model[a[pn]]):
            start_val = model[s[pn]].as_long()
            end_val = model[e[pn]].as_long()
            meetings.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": start_val,
                "end": end_val
            })

    # Sort by start times
    meetings.sort(key=lambda x: x["start"])

    # Format to required JSON structure
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": fmt_time(m["start"]),
            "end_time": fmt_time(m["end"])
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()