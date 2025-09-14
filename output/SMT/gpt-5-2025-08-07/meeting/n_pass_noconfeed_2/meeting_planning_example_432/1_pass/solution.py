import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, is_true, sat

def minutes_to_hm(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations
    GGP = "Golden Gate Park"
    FW = "Fisherman's Wharf"
    BV = "Bayview"
    MD = "Mission District"
    EM = "Embarcadero"
    FD = "Financial District"

    # Travel times (in minutes), as provided
    travel = {
        (GGP, FW): 24,
        (GGP, BV): 23,
        (GGP, MD): 17,
        (GGP, EM): 25,
        (GGP, FD): 26,
        (FW, GGP): 25,
        (FW, BV): 26,
        (FW, MD): 22,
        (FW, EM): 8,
        (FW, FD): 11,
        (BV, GGP): 22,
        (BV, FW): 25,
        (BV, MD): 13,
        (BV, EM): 19,
        (BV, FD): 19,
        (MD, GGP): 17,
        (MD, FW): 22,
        (MD, BV): 15,
        (MD, EM): 19,
        (MD, FD): 17,
        (EM, GGP): 25,
        (EM, FW): 6,
        (EM, BV): 21,
        (EM, MD): 20,
        (EM, FD): 5,
        (FD, GGP): 23,
        (FD, FW): 10,
        (FD, BV): 19,
        (FD, MD): 17,
        (FD, EM): 4,
    }

    # Input parameters and constraints
    start_location = GGP
    start_time = 9 * 60  # 9:00

    persons = [
        {
            "name": "Joseph",
            "location": FW,
            "avail_start": 8 * 60,           # 8:00
            "avail_end": 17 * 60 + 30,       # 17:30
            "min_duration": 90,
        },
        {
            "name": "Jeffrey",
            "location": BV,
            "avail_start": 17 * 60 + 30,     # 17:30
            "avail_end": 21 * 60 + 30,       # 21:30
            "min_duration": 60,
        },
        {
            "name": "Kevin",
            "location": MD,
            "avail_start": 11 * 60 + 15,     # 11:15
            "avail_end": 15 * 60 + 15,       # 15:15
            "min_duration": 30,
        },
        {
            "name": "David",
            "location": EM,
            "avail_start": 8 * 60 + 15,      # 8:15
            "avail_end": 9 * 60,             # 9:00
            "min_duration": 30,
        },
        {
            "name": "Barbara",
            "location": FD,
            "avail_start": 10 * 60 + 30,     # 10:30
            "avail_end": 16 * 60 + 30,       # 16:30
            "min_duration": 15,
        },
    ]

    # Z3 optimization model
    opt = Optimize()
    opt.set(priority='lex')  # Lexicographic optimization

    # Variables per person
    vars_by_person = {}
    for p in persons:
        s = Int(f"s_{p['name']}")
        e = Int(f"e_{p['name']}")
        m = Bool(f"m_{p['name']}")
        vars_by_person[p['name']] = (s, e, m)

        # General bounds for times
        opt.add(s >= 0, s <= 24 * 60)
        opt.add(e >= 0, e <= 24 * 60)

        # Meeting feasibility when chosen to meet
        origin_travel = travel[(start_location, p["location"])]
        opt.add(Implies(m, And(
            s >= p["avail_start"],
            e <= p["avail_end"],
            e - s >= p["min_duration"],
            s >= start_time + origin_travel
        )))

    # Pairwise non-overlap with travel time between meetings
    n = len(persons)
    for i in range(n):
        for j in range(i + 1, n):
            pi = persons[i]
            pj = persons[j]
            si, ei, mi = vars_by_person[pi["name"]]
            sj, ej, mj = vars_by_person[pj["name"]]
            tij = travel[(pi["location"], pj["location"])]
            tji = travel[(pj["location"], pi["location"])]
            opt.add(Implies(And(mi, mj), Or(
                ei + tij <= sj,
                ej + tji <= si
            )))

    # Objectives:
    meet_flags = [vars_by_person[p["name"]][2] for p in persons]
    meet_count = Sum([If(m, 1, 0) for m in meet_flags])

    durations_sum = Sum([If(m, vars_by_person[p["name"]][1] - vars_by_person[p["name"]][0], 0) for p in persons])

    # Last end time (for tie-breaking to prefer earlier finish)
    last_end = Int("last_end")
    opt.add(last_end >= 0, last_end <= 24 * 60)
    for p in persons:
        s, e, m = vars_by_person[p["name"]]
        opt.add(Implies(m, e <= last_end))

    opt.maximize(meet_count)
    opt.maximize(durations_sum)
    opt.minimize(last_end)

    result = {"itinerary": []}

    if opt.check() == sat:
        model = opt.model()
        meetings = []
        for p in persons:
            s, e, m = vars_by_person[p["name"]]
            if is_true(model.evaluate(m)):
                start_val = model.evaluate(s).as_long()
                end_val = model.evaluate(e).as_long()
                meetings.append({
                    "action": "meet",
                    "location": p["location"],
                    "person": p["name"],
                    "start_time": minutes_to_hm(start_val),
                    "end_time": minutes_to_hm(end_val)
                })
        # Sort meetings by start time
        meetings.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
        result["itinerary"] = meetings

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()