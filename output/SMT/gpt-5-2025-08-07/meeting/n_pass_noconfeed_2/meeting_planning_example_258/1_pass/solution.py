"""SOLUTION:"""
import json
import itertools
from z3 import Optimize, Int, Sum, If, sat

def minutes(h, m):
    return h * 60 + m

def m2str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def solve_order(order, people, travel, start_location, start_time):
    k = len(order)
    opt = Optimize()
    starts = [Int(f"start_{i}") for i in range(k)]
    ends = [Int(f"end_{i}") for i in range(k)]

    for i in range(k):
        p = people[order[i]]
        opt.add(starts[i] >= 0, ends[i] >= 0)
        # Meeting within availability
        opt.add(starts[i] >= p['start'])
        opt.add(ends[i] <= p['end'])
        opt.add(ends[i] - starts[i] >= p['min'])

    # Travel and initial arrival constraints
    waits = []
    if k > 0:
        first_loc = people[order[0]]['location']
        initial_arrival = start_time + travel[start_location][first_loc]
        opt.add(starts[0] >= initial_arrival)
        # Waiting before first meeting
        max0 = max(initial_arrival, people[order[0]]['start'])
        waits.append(starts[0] - max0)

    for i in range(k - 1):
        loc_i = people[order[i]]['location']
        loc_j = people[order[i + 1]]['location']
        travel_ij = travel[loc_i][loc_j]
        # Next meeting cannot start before travel completion and next availability
        # start_{i+1} >= end_i + travel_ij
        opt.add(starts[i + 1] >= ends[i] + travel_ij)
        # Waiting between meetings:
        # wait = start_{i+1} - max(end_i + travel_ij, avail_start_{i+1})
        next_avail = people[order[i + 1]]['start']
        waits.append(starts[i + 1] - If(ends[i] + travel_ij >= next_avail, ends[i] + travel_ij, next_avail))

    # Objective: maximize total meeting time, then minimize total waiting time
    total_meeting = Sum([ends[i] - starts[i] for i in range(k)]) if k > 0 else Int("zero_meeting")
    if k == 0:
        opt.add(total_meeting == 0)
    total_wait = Sum(waits) if waits else Int("zero_wait")
    if not waits:
        opt.add(total_wait == 0)

    opt.maximize(total_meeting)
    opt.minimize(total_wait)

    if opt.check() != sat:
        return None

    model = opt.model()
    itinerary = []
    for i in range(k):
        p = people[order[i]]
        s = model.eval(starts[i]).as_long()
        e = model.eval(ends[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": p['location'],
            "person": p['name'],
            "start_time": m2str(s),
            "end_time": m2str(e)
        })
    sum_dur = sum([model.eval(ends[i]).as_long() - model.eval(starts[i]).as_long() for i in range(k)]) if k > 0 else 0
    last_end = model.eval(ends[-1]).as_long() if k > 0 else start_time
    return {"itinerary": itinerary, "sum_dur": sum_dur, "last_end": last_end, "count": k}

def main():
    # Locations and directed travel times (in minutes)
    travel = {
        "Embarcadero": {
            "Presidio": 20,
            "Richmond District": 21,
            "Fisherman's Wharf": 6
        },
        "Presidio": {
            "Embarcadero": 20,
            "Richmond District": 7,
            "Fisherman's Wharf": 19
        },
        "Richmond District": {
            "Embarcadero": 19,
            "Presidio": 7,
            "Fisherman's Wharf": 18
        },
        "Fisherman's Wharf": {
            "Embarcadero": 8,
            "Presidio": 17,
            "Richmond District": 18
        }
    }

    # People with availability and minimum meeting durations
    people = [
        {
            "name": "Betty",
            "location": "Presidio",
            "start": minutes(10, 15),
            "end": minutes(21, 30),
            "min": 45
        },
        {
            "name": "David",
            "location": "Richmond District",
            "start": minutes(13, 0),
            "end": minutes(20, 15),
            "min": 90
        },
        {
            "name": "Barbara",
            "location": "Fisherman's Wharf",
            "start": minutes(9, 15),
            "end": minutes(20, 15),
            "min": 120
        }
    ]

    start_location = "Embarcadero"
    start_time = minutes(9, 0)

    best = None
    best_metrics = None

    indices = list(range(len(people)))
    for r in range(1, len(people) + 1):
        for perm in itertools.permutations(indices, r):
            res = solve_order(perm, people, travel, start_location, start_time)
            if res is None:
                continue
            metrics = (res["count"], res["sum_dur"], -res["last_end"])
            if best is None or metrics > best_metrics:
                best = res
                best_metrics = metrics

    output = {"itinerary": []}
    if best is not None:
        output["itinerary"] = best["itinerary"]

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()