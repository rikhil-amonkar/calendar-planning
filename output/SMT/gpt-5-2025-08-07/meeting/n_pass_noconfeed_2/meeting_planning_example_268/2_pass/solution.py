import json
from z3 import Optimize, Int, Bool, If, Implies, And, Not, is_true, sat

def minutes_to_time_str_from_9am(m):
    # Convert minutes since 9:00 to 24-hour "H:MM" without leading zero on hour
    total_minutes = 9 * 60 + m
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Locations
    GGP = "Golden Gate Park"
    AS = "Alamo Square"
    PR = "Presidio"
    RH = "Russian Hill"

    # Travel times (minutes), directed
    travel = {
        (GGP, AS): 10,
        (GGP, PR): 11,
        (GGP, RH): 19,
        (AS, GGP): 9,
        (AS, PR): 18,
        (AS, RH): 13,
        (PR, GGP): 12,
        (PR, AS): 18,
        (PR, RH): 14,
        (RH, GGP): 21,
        (RH, AS): 15,
        (RH, PR): 14,
    }

    # Participants with availability windows relative to 9:00
    # Window: [start, end], end is hard cutoff for meeting end
    people = [
        {
            "name": "Timothy",
            "location": AS,
            "start": 180,  # 12:00
            "end": 435,    # 16:15
            "min_dur": 105
        },
        {
            "name": "Mark",
            "location": PR,
            "start": 585,  # 18:45
            "end": 720,    # 21:00
            "min_dur": 60
        },
        {
            "name": "Joseph",
            "location": RH,
            "start": 465,  # 16:45
            "end": 750,    # 21:30
            "min_dur": 60
        },
    ]

    # Planning horizon in minutes since 9:00
    horizon = 800

    opt = Optimize()
    # Ensure lexicographic optimization: maximize number of meetings first, then minimize L
    opt.set(priority='lex')

    # Variables per person
    vars_by_person = {}
    for p in people:
        meet = Bool(f"meet_{p['name']}")
        s = Int(f"s_{p['name']}")  # start time (minutes since 9:00)
        e = Int(f"e_{p['name']}")  # end time
        d = Int(f"d_{p['name']}")  # duration
        vars_by_person[p['name']] = {"meet": meet, "s": s, "e": e, "d": d}

        # Time bounds
        opt.add(s >= 0, s <= horizon)
        opt.add(e >= 0, e <= horizon)

        # Duration equals minimum required if meeting, else zero
        opt.add(If(meet, d == p["min_dur"], d == 0))

        # End equals start + duration
        opt.add(e == s + d)

        # Availability constraints if meeting
        opt.add(Implies(meet, s >= p["start"]))
        opt.add(Implies(meet, e <= p["end"]))

        # Must be reachable from starting location (Golden Gate Park) at 9:00
        opt.add(Implies(meet, s >= travel[(GGP, p["location"])]))

    # Pairwise ordering constraints with travel times
    def order_var(i_name, j_name):
        return Bool(f"order_{i_name}_before_{j_name}")

    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            vi = vars_by_person[pi["name"]]
            vj = vars_by_person[pj["name"]]
            oij = order_var(pi["name"], pj["name"])

            # If both meetings occur and i before j, then respect travel time i->j
            opt.add(Implies(And(vi["meet"], vj["meet"], oij),
                            vj["s"] >= vi["e"] + travel[(pi["location"], pj["location"])]))
            # If both meetings occur and j before i, then respect travel time j->i
            opt.add(Implies(And(vi["meet"], vj["meet"], Not(oij)),
                            vi["s"] >= vj["e"] + travel[(pj["location"], pi["location"])]))

    # Objective 1: maximize number of people met
    meet_sum = sum([If(vars_by_person[p["name"]]["meet"], 1, 0) for p in people])
    opt.maximize(meet_sum)

    # Objective 2: minimize makespan (latest meeting end time among those met)
    L = Int("makespan")
    opt.add(L >= 0, L <= horizon)
    for p in people:
        v = vars_by_person[p["name"]]
        # If meeting, e <= L and L >= e; with minimization, L becomes the max end
        opt.add(Implies(v["meet"], v["e"] <= L))
        opt.add(Implies(v["meet"], L >= v["e"]))
    opt.minimize(L)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    # Build itinerary from model
    itinerary = []
    for p in people:
        v = vars_by_person[p["name"]]
        if is_true(m.evaluate(v["meet"])):
            start_min = m.evaluate(v["s"]).as_long()
            end_min = m.evaluate(v["e"]).as_long()
            itinerary.append({
                "person": p["name"],
                "location": p["location"],
                "start_min": start_min,
                "end_min": end_min
            })

    # Sort by start time
    itinerary.sort(key=lambda x: x["start_min"])

    # Format output
    output_itinerary = []
    for item in itinerary:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time_str_from_9am(item["start_min"]),
            "end_time": minutes_to_time_str_from_9am(item["end_min"]),
        })

    print(json.dumps({"itinerary": output_itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    # The response must start with 'SOLUTION:'
    # Print prefix then the JSON from the solver
    print("SOLUTION:")
    main()