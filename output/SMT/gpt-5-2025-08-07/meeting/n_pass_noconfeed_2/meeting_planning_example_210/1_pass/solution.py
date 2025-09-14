from z3 import *
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    FW = "Fisherman's Wharf"
    PR = "Presidio"
    RD = "Richmond District"
    FD = "Financial District"

    # Travel times in minutes (directed)
    travel = {
        (FW, PR): 17,
        (FW, RD): 18,
        (FW, FD): 11,
        (PR, FW): 19,
        (PR, RD): 7,
        (PR, FD): 23,
        (RD, FW): 18,
        (RD, PR): 7,
        (RD, FD): 22,
        (FD, FW): 10,
        (FD, PR): 22,
        (FD, RD): 21,
    }

    # Start at Fisherman's Wharf at 9:00
    start_loc = FW
    arrival_time = minutes(9, 0)

    # People and their constraints
    people = [
        {
            "name": "Emily",
            "location": PR,
            "avail_start": minutes(16, 15),
            "avail_end": minutes(21, 0),
            "min_duration": 105
        },
        {
            "name": "Joseph",
            "location": RD,
            "avail_start": minutes(17, 15),
            "avail_end": minutes(22, 0),
            "min_duration": 120
        },
        {
            "name": "Melissa",
            "location": FD,
            "avail_start": minutes(15, 45),
            "avail_end": minutes(21, 45),
            "min_duration": 75
        }
    ]

    # Z3 variables
    opt = Optimize()
    vars_map = {}

    for p in people:
        name = p["name"]
        s = Int(f"s_{name}")
        e = Int(f"e_{name}")
        meet = Bool(f"meet_{name}")
        vars_map[name] = {"s": s, "e": e, "meet": meet, "loc": p["location"]}

        # Bounds for times
        opt.add(s >= 0, s <= 24 * 60, e >= 0, e <= 24 * 60)

        # If meeting, respect availability, minimum duration, and arrival from start location
        opt.add(Implies(meet, And(
            s >= p["avail_start"],
            e <= p["avail_end"],
            e - s >= p["min_duration"],
            s >= arrival_time + travel[(start_loc, p["location"])]
        )))
        # If not meeting, set zero-length interval (harmless)
        opt.add(Implies(Not(meet), e == s))

    # No overlap with travel between any pair of meetings
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            si = vars_map[pi["name"]]["s"]
            ei = vars_map[pi["name"]]["e"]
            mi = vars_map[pi["name"]]["meet"]
            sj = vars_map[pj["name"]]["s"]
            ej = vars_map[pj["name"]]["e"]
            mj = vars_map[pj["name"]]["meet"]
            li = pi["location"]
            lj = pj["location"]
            tij = travel[(li, lj)]
            tji = travel[(lj, li)]
            # Either not both meetings happen, or one finishes with travel before the other starts
            opt.add(Or(Not(mi), Not(mj),
                       ei + tij <= sj,
                       ej + tji <= si))

    # Objective: maximize number of meetings, then total meeting time
    meet_count = Sum([If(vars_map[p["name"]]["meet"], 1, 0) for p in people])
    total_meeting_minutes = Sum([If(vars_map[p["name"]]["meet"], vars_map[p["name"]]["e"] - vars_map[p["name"]]["s"], 0) for p in people])

    h1 = opt.maximize(meet_count)
    h2 = opt.maximize(total_meeting_minutes)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary
    itinerary = []
    for p in people:
        name = p["name"]
        s = model[vars_map[name]["s"]].as_long()
        e = model[vars_map[name]["e"]].as_long()
        meet = is_true(model[vars_map[name]["meet"]])
        if meet:
            itinerary.append({
                "action": "meet",
                "location": vars_map[name]["loc"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()