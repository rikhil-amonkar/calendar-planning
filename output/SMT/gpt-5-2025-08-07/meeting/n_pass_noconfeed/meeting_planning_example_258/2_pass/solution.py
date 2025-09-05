import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, Implies, sat, is_true

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    E = "Embarcadero"
    P = "Presidio"
    R = "Richmond District"
    F = "Fisherman's Wharf"

    # Travel times in minutes (directed)
    travel = {
        E: {P: 20, R: 21, F: 6,  E: 0},
        P: {E: 20, R: 7,  F: 19, P: 0},
        R: {E: 19, P: 7,  F: 18, R: 0},
        F: {E: 8,  P: 17, R: 18, F: 0},
    }

    # People data: location, availability start, availability end, minimum duration
    people = {
        "Betty":   {"location": P, "avail_start": minutes(10, 15), "avail_end": minutes(21, 30), "min_dur": 45},
        "David":   {"location": R, "avail_start": minutes(13, 0),  "avail_end": minutes(20, 15), "min_dur": 90},
        "Barbara": {"location": F, "avail_start": minutes(9, 15),  "avail_end": minutes(20, 15), "min_dur": 120},
    }

    start_location = E
    arrival_time = minutes(9, 0)

    # Z3 variables
    opt = Optimize()
    opt.set(priority="lex")

    meet = {}
    s = {}
    d = {}
    e = {}

    for person, info in people.items():
        meet[person] = Bool(f"meet_{person}")
        s[person] = Int(f"s_{person}")   # start time in minutes from midnight
        d[person] = Int(f"d_{person}")   # duration
        e[person] = Int(f"e_{person}")   # end = start + duration

        # Basic bounds
        opt.add(s[person] >= 0, d[person] >= 0, e[person] >= 0)
        opt.add(e[person] == s[person] + d[person])

        # If meeting them, enforce availability and minimum duration
        opt.add(Implies(meet[person], s[person] >= info["avail_start"]))
        opt.add(Implies(meet[person], e[person] <= info["avail_end"]))
        opt.add(Implies(meet[person], d[person] >= info["min_dur"]))

        # If not meeting, duration is 0
        opt.add(Implies(Not(meet[person]), d[person] == 0))

        # You must be able to get to their location from initial arrival (lower bound)
        opt.add(Implies(meet[person],
                        s[person] >= arrival_time + travel[start_location][info["location"]]))

    # Pairwise non-overlap plus travel-time separation (total ordering with travel)
    people_list = list(people.keys())
    for i in range(len(people_list)):
        for j in range(i + 1, len(people_list)):
            p_i = people_list[i]
            p_j = people_list[j]
            loc_i = people[p_i]["location"]
            loc_j = people[p_j]["location"]

            # If both are met, either i before j with travel time or j before i with travel time
            opt.add(Implies(And(meet[p_i], meet[p_j]),
                            Or(e[p_i] + travel[loc_i][loc_j] <= s[p_j],
                               e[p_j] + travel[loc_j][loc_i] <= s[p_i])))

    # Objectives:
    # 1) Maximize the number of friends met
    attend_count = Sum([If(meet[p], 1, 0) for p in people_list])
    opt.maximize(attend_count)

    # 2) Maximize total meeting time
    total_meeting_time = Sum([d[p] for p in people_list])
    opt.maximize(total_meeting_time)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    # Build itinerary from model
    itinerary = []
    for person in people_list:
        if is_true(model.evaluate(meet[person], model_completion=True)):
            start_min = model.evaluate(s[person], model_completion=True).as_long()
            end_min = model.evaluate(e[person], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[person]["location"],
                "person": person,
                "start_time": minutes_to_str(start_min),
                "end_time": minutes_to_str(end_min),
            })

    # Sort by start time
    def to_minutes(tstr):
        h, m = map(int, tstr.split(":"))
        return h * 60 + m

    itinerary.sort(key=lambda x: to_minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()