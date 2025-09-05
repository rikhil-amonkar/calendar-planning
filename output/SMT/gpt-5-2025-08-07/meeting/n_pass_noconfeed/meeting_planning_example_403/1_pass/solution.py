import json
from z3 import *

def time_to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    locations = [
        "Union Square",
        "Golden Gate Park",
        "Pacific Heights",
        "Presidio",
        "Chinatown",
        "The Castro"
    ]

    # Travel times in minutes (directed)
    travel = {
        "Union Square": {
            "Golden Gate Park": 22,
            "Pacific Heights": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "The Castro": 19,
        },
        "Golden Gate Park": {
            "Union Square": 22,
            "Pacific Heights": 16,
            "Presidio": 11,
            "Chinatown": 23,
            "The Castro": 13,
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Golden Gate Park": 15,
            "Presidio": 11,
            "Chinatown": 11,
            "The Castro": 16,
        },
        "Presidio": {
            "Union Square": 22,
            "Golden Gate Park": 12,
            "Pacific Heights": 11,
            "Chinatown": 21,
            "The Castro": 21,
        },
        "Chinatown": {
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Pacific Heights": 10,
            "Presidio": 19,
            "The Castro": 22,
        },
        "The Castro": {
            "Union Square": 19,
            "Golden Gate Park": 11,
            "Pacific Heights": 16,
            "Presidio": 20,
            "Chinatown": 20,
        },
    }

    # People and constraints
    people = [
        {
            "name": "Andrew",
            "location": "Golden Gate Park",
            "avail_start": time_to_minutes(11,45),
            "avail_end": time_to_minutes(14,30),
            "min_duration": 75
        },
        {
            "name": "Sarah",
            "location": "Pacific Heights",
            "avail_start": time_to_minutes(16,15),
            "avail_end": time_to_minutes(18,45),
            "min_duration": 15
        },
        {
            "name": "Nancy",
            "location": "Presidio",
            "avail_start": time_to_minutes(17,30),
            "avail_end": time_to_minutes(19,15),
            "min_duration": 60
        },
        {
            "name": "Rebecca",
            "location": "Chinatown",
            "avail_start": time_to_minutes(9,45),
            "avail_end": time_to_minutes(21,30),
            "min_duration": 90
        },
        {
            "name": "Robert",
            "location": "The Castro",
            "avail_start": time_to_minutes(8,30),
            "avail_end": time_to_minutes(14,15),
            "min_duration": 30
        },
    ]

    # Day parameters
    start_loc = "Union Square"
    arrival_time = time_to_minutes(9, 0)
    day_end = max(p["avail_end"] for p in people)

    opt = Optimize()

    # Decision variables per person
    meets = {}
    starts = {}
    ends = {}
    durs = {}

    for p in people:
        name = p["name"]
        meets[name] = Bool(f"meet_{name}")
        starts[name] = Int(f"start_{name}")
        ends[name] = Int(f"end_{name}")
        durs[name] = Int(f"dur_{name}")

        # Basic bounds
        opt.add(starts[name] >= arrival_time)
        opt.add(ends[name] <= day_end)
        opt.add(durs[name] >= 0)
        opt.add(ends[name] == starts[name] + durs[name])

        # Availability and minimum duration if meeting
        opt.add(Implies(meets[name], starts[name] >= p["avail_start"]))
        opt.add(Implies(meets[name], ends[name] <= p["avail_end"]))
        opt.add(Implies(meets[name], durs[name] >= p["min_duration"]))

        # Ensure reachability from starting point (for earliest feasible start)
        # If meeting, you must be able to get there from Union Square after arrival.
        opt.add(Implies(meets[name],
                        starts[name] >= arrival_time + travel[start_loc][p["location"]]))

        # If not meeting, set duration to 0 to avoid unnecessary inflation
        opt.add(Implies(Not(meets[name]), durs[name] == 0))

    # Non-overlap and travel time between meetings
    for i in range(len(people)):
        for j in range(i+1, len(people)):
            pi = people[i]
            pj = people[j]
            ni = pi["name"]
            nj = pj["name"]
            li = pi["location"]
            lj = pj["location"]

            tij = travel[li][lj]
            tji = travel[lj][li]

            # If both are met, then either i before j with required travel, or j before i with required travel
            opt.add(Implies(And(meets[ni], meets[nj]),
                            Or(starts[nj] >= ends[ni] + tij,
                               starts[ni] >= ends[nj] + tji)))

    # Objective: maximize number of meetings, then total meeting time
    total_meet_count = Sum([If(meets[p["name"]], IntVal(1), IntVal(0)) for p in people])
    total_meet_minutes = Sum([durs[p["name"]] for p in people])

    # Weight to prioritize meeting count strongly over minutes
    objective = total_meet_count * 100000 + total_meet_minutes
    opt.maximize(objective)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary
    itinerary = []
    for p in people:
        name = p["name"]
        if is_true(model[meets[name]]):
            s = model[starts[name]].as_long()
            e = model[ends[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()