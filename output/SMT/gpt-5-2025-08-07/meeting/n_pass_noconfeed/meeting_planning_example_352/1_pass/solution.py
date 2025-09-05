import json
from z3 import Optimize, Int, Bool, Sum, If, And, Or, Xor, Implies, sat

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    USQ = "Union Square"
    NOB = "Nob Hill"
    HAI = "Haight-Ashbury"
    CHI = "Chinatown"
    MAR = "Marina District"

    # Travel times (directed, in minutes)
    travel = {
        USQ: {USQ:0, NOB:9, HAI:18, CHI:7, MAR:18},
        NOB: {USQ:7, NOB:0, HAI:13, CHI:6, MAR:11},
        HAI: {USQ:17, NOB:15, HAI:0, CHI:19, MAR:17},
        CHI: {USQ:7, NOB:8, HAI:19, CHI:0, MAR:12},
        MAR: {USQ:16, NOB:12, HAI:16, CHI:16, MAR:0},
    }

    # Arrival time at Union Square (9:00 AM)
    origin_time = 9 * 60  # 540

    # People and constraints
    people = [
        {"id": 0, "name": "Karen",  "location": NOB, "avail_start": 21*60 + 15, "avail_end": 21*60 + 45, "min_dur": 30},
        {"id": 1, "name": "Joseph", "location": HAI, "avail_start": 12*60 + 30, "avail_end": 19*60 + 45, "min_dur": 90},
        {"id": 2, "name": "Sandra", "location": CHI, "avail_start": 7*60 + 15,  "avail_end": 19*60 + 15, "min_dur": 75},
        {"id": 3, "name": "Nancy",  "location": MAR, "avail_start": 11*60,      "avail_end": 20*60 + 15, "min_dur": 105},
    ]

    n = len(people)

    opt = Optimize()
    opt.set(priority='lex')

    # Variables
    meet = [Bool(f"meet_{i}") for i in range(n)]
    s = [Int(f"start_{i}") for i in range(n)]
    e = [Int(f"end_{i}") for i in range(n)]

    # After-order variables: after[i][j] means meeting j starts after meeting i ends plus travel(i->j)
    after = [[Bool(f"after_{i}_{j}") if i != j else None for j in range(n)] for i in range(n)]

    # Domain constraints
    for i, p in enumerate(people):
        opt.add(s[i] >= 0, s[i] <= 24*60)
        opt.add(e[i] >= 0, e[i] <= 24*60)
        # Meeting constraints
        opt.add(Implies(meet[i], And(
            s[i] >= p["avail_start"],
            e[i] <= p["avail_end"],
            e[i] - s[i] >= p["min_dur"]
        )))
        # If not met, zero-length at 0 for cleanliness
        opt.add(Implies(~meet[i], And(s[i] == 0, e[i] == 0)))
        # Must be reachable from origin
        opt.add(Implies(meet[i], s[i] >= origin_time + travel[USQ][p["location"]]))

    # Non-overlap and travel between meetings
    for i in range(n):
        for j in range(i+1, n):
            # If both are met, exactly one order holds
            opt.add(Implies(And(meet[i], meet[j]), Xor(after[i][j], after[j][i])))
            # If one or both not met, no order enforced
            opt.add(Implies(~And(meet[i], meet[j]), And(~after[i][j], ~after[j][i])))

            # Travel time implications
            loc_i = people[i]["location"]
            loc_j = people[j]["location"]
            opt.add(Implies(after[i][j], s[j] >= e[i] + travel[loc_i][loc_j]))
            opt.add(Implies(after[j][i], s[i] >= e[j] + travel[loc_j][loc_i]))

    # Objectives
    num_met = Sum([If(meet[i], 1, 0) for i in range(n)])
    total_minutes = Sum([If(meet[i], e[i] - s[i], 0) for i in range(n)])
    opt.maximize(num_met)
    opt.maximize(total_minutes)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    # Build itinerary: filter met, extract times, sort by start
    items = []
    for i, p in enumerate(people):
        if m.evaluate(meet[i], model_completion=True):
            start_val = m.evaluate(s[i]).as_long()
            end_val = m.evaluate(e[i]).as_long()
            items.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time_min": start_val,
                "end_time_min": end_val
            })

    items.sort(key=lambda x: x["start_time_min"])

    # Format times
    itinerary = []
    for it in items:
        itinerary.append({
            "action": "meet",
            "location": it["location"],
            "person": it["person"],
            "start_time": minutes_to_str(it["start_time_min"]),
            "end_time": minutes_to_str(it["end_time_min"])
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()