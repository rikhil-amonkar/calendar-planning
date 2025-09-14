#!/usr/bin/env python3
import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, sat, Sum

def minutes_to_time(m):
    h = m // 60
    m_rem = m % 60
    return f"{h}:{m_rem:02d}"

def main():
    travel = {
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Bayview"): 26,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Bayview"): 15,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Mission District"): 13
    }

    friend_data = [
        {
            "name": "Sarah",
            "location": "Fisherman's Wharf",
            "avail_start": 885,
            "avail_end": 1050,
            "min_duration": 105
        },
        {
            "name": "Mary",
            "location": "Richmond District",
            "avail_start": 780,
            "avail_end": 1155,
            "min_duration": 75
        },
        {
            "name": "Helen",
            "location": "Mission District",
            "avail_start": 1305,
            "avail_end": 1350,
            "min_duration": 30
        },
        {
            "name": "Thomas",
            "location": "Bayview",
            "avail_start": 915,
            "avail_end": 1125,
            "min_duration": 120
        }
    ]

    n = len(friend_data)
    opt = Optimize()

    sched = [Bool(f"sched_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    for i in range(n):
        fd = friend_data[i]
        opt.add(
            If(
                sched[i],
                And(
                    start_vars[i] >= fd["avail_start"],
                    end_vars[i] <= fd["avail_end"],
                    end_vars[i] - start_vars[i] >= fd["min_duration"],
                    order_vars[i] >= 0,
                    order_vars[i] <= n - 1
                ),
                And(start_vars[i] == 0, end_vars[i] == 0, order_vars[i] == -1)
            )
        )

    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(sched[i], sched[j]), order_vars[i] != order_vars[j]))

    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = friend_data[i]["location"]
                loc_j = friend_data[j]["location"]
                travel_time = travel.get((loc_i, loc_j), 9999)
                opt.add(
                    Implies(
                        And(sched[i], sched[j], order_vars[i] < order_vars[j]),
                        start_vars[j] >= end_vars[i] + travel_time
                    )
                )

    starting_time = 540
    for i in range(n):
        loc = friend_data[i]["location"]
        travel_from_start = travel.get(("Haight-Ashbury", loc), 9999)
        opt.add(
            Implies(
                And(sched[i], order_vars[i] == 0),
                start_vars[i] >= starting_time + travel_from_start
            )
        )

    total_meetings = Sum([If(sched[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        meetings = []
        for i in range(n):
            if model.eval(sched[i]):
                meetings.append((model.eval(order_vars[i]).as_long(), i))
        meetings.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, i in meetings:
            fd = friend_data[i]
            start_time = model.eval(start_vars[i]).as_long()
            end_time = model.eval(end_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": fd["location"],
                "person": fd["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()