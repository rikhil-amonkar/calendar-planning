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
    locations = ["Bayview", "Embarcadero", "Fisherman's Wharf", "Financial District"]

    # Travel times (in minutes)
    travel = {
        "Bayview": {
            "Embarcadero": 19,
            "Fisherman's Wharf": 25,
            "Financial District": 19,
        },
        "Embarcadero": {
            "Bayview": 21,
            "Fisherman's Wharf": 6,
            "Financial District": 5,
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Embarcadero": 8,
            "Financial District": 11,
        },
        "Financial District": {
            "Bayview": 19,
            "Embarcadero": 4,
            "Fisherman's Wharf": 10,
        }
    }

    # People, locations, availability windows, and minimum meeting durations
    people = {
        "Betty": {
            "location": "Embarcadero",
            "avail_start": minutes(19, 45),  # 7:45 PM
            "avail_end": minutes(21, 45),    # 9:45 PM
            "min_duration": 15
        },
        "Karen": {
            "location": "Fisherman's Wharf",
            "avail_start": minutes(8, 45),   # 8:45 AM
            "avail_end": minutes(15, 0),     # 3:00 PM
            "min_duration": 30
        },
        "Anthony": {
            "location": "Financial District",
            "avail_start": minutes(9, 15),   # 9:15 AM
            "avail_end": minutes(21, 30),    # 9:30 PM
            "min_duration": 105
        }
    }

    start_location = "Bayview"
    arrival_time_start = minutes(9, 0)  # 9:00 AM

    # Z3 variables
    opt = Optimize()
    opt.set(priority='lex')

    s = {}
    e = {}
    met = {}
    order = {}

    for person in people:
        s[person] = Int(f"s_{person}")
        e[person] = Int(f"e_{person}")
        met[person] = Bool(f"met_{person}")
        order[person] = Int(f"order_{person}")

        # Time bounds within a day
        opt.add(s[person] >= 0, s[person] <= 24*60)
        opt.add(e[person] >= 0, e[person] <= 24*60)

        # If meeting, must respect availability and minimum duration
        opt.add(Implies(met[person],
                        And(s[person] >= people[person]["avail_start"],
                            e[person] <= people[person]["avail_end"],
                            e[person] - s[person] >= people[person]["min_duration"])))

        # Order encoding with nMet will constrain order further
        opt.add(Implies(Not(met[person]), order[person] == 0))

    # Number of meetings
    nMet = Int("nMet")
    opt.add(nMet >= 0, nMet <= len(people))
    opt.add(nMet == Sum([If(met[p], 1, 0) for p in people]))

    # Orders must be 1..nMet and consecutive without gaps
    for p in people:
        opt.add(Implies(met[p], And(order[p] >= 1, order[p] <= nMet)))

    # Ensure that for each k, exactly one person has order k if k <= nMet, else none
    for k in range(1, len(people) + 1):
        opt.add(Sum([If(order[p] == k, 1, 0) for p in people]) == If(k <= nMet, 1, 0))

    # Travel constraints:
    # If first meeting, leave from start location at arrival_time_start and travel accordingly
    for p in people:
        loc_p = people[p]["location"]
        opt.add(Implies(order[p] == 1, s[p] >= arrival_time_start + travel[start_location][loc_p]))

    # For consecutive meetings, ensure travel time between locations is respected
    plist = list(people.keys())
    for i in range(len(plist)):
        p_i = plist[i]
        loc_i = people[p_i]["location"]
        for j in range(len(plist)):
            if i == j:
                continue
            p_j = plist[j]
            loc_j = people[p_j]["location"]
            tij = travel[loc_j][loc_i]
            opt.add(Implies(order[p_i] == order[p_j] + 1, s[p_i] >= e[p_j] + tij))

    # Objectives: maximize number of meetings, then total meeting duration
    total_duration = Sum([If(met[p], e[p] - s[p], 0) for p in people])
    opt.maximize(nMet)
    opt.maximize(total_duration)

    # Solve
    if opt.check() != sat:
        # No feasible plan; output empty itinerary
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    # Extract meetings and sort by order
    meetings = []
    for p in people:
        if m.evaluate(met[p], model_completion=True):
            start = m.evaluate(s[p], model_completion=True).as_long()
            end = m.evaluate(e[p], model_completion=True).as_long()
            ord_val = m.evaluate(order[p], model_completion=True).as_long()
            meetings.append((ord_val, {
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": fmt_time(start),
                "end_time": fmt_time(end)
            }))

    meetings.sort(key=lambda x: x[0])

    itinerary = [item for _, item in meetings]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()