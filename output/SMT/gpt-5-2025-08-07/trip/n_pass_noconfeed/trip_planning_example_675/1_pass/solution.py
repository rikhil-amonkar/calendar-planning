import json
from z3 import *

def solve_itinerary():
    # Problem parameters
    days_total = 16
    cities = ["Munich", "Porto", "Split", "Milan", "Dubrovnik", "Krakow"]
    city_idx = {name: i for i, name in enumerate(cities)}
    MUNICH = city_idx["Munich"]
    PORTO = city_idx["Porto"]
    SPLIT = city_idx["Split"]
    MILAN = city_idx["Milan"]
    DUBROVNIK = city_idx["Dubrovnik"]
    KRAKOW = city_idx["Krakow"]

    # Direct flight adjacency (undirected)
    edges = [
        (MUNICH, PORTO),
        (SPLIT, MILAN),
        (MILAN, PORTO),
        (MUNICH, KRAKOW),
        (MUNICH, MILAN),
        (DUBROVNIK, MUNICH),
        (KRAKOW, SPLIT),
        (KRAKOW, MILAN),
        (MUNICH, SPLIT),
    ]
    adj = set()
    for (a, b) in edges:
        adj.add((a, b))
        adj.add((b, a))

    # Desired durations (targets)
    targets = {
        DUBROVNIK: 4,  # "plan to stay" - strong
        SPLIT: 3,      # "would like" - medium
        MILAN: 3,      # "would like" - medium (plus wedding window)
        PORTO: 4,      # "want to spend" - strong
        KRAKOW: 2,     # "would like" - medium (plus friends window)
        MUNICH: 5,     # "plan to stay" - strong (show days suggest 5)
    }

    # Weights for deviation importance
    strong_weight = 5
    medium_weight = 3
    weights = {
        DUBROVNIK: strong_weight,
        PORTO: strong_weight,
        MUNICH: strong_weight,
        MILAN: medium_weight,
        SPLIT: medium_weight,
        KRAKOW: medium_weight,
    }

    # Z3 variables
    Start = [Int(f"start_{d+1}") for d in range(days_total)]
    End = [Int(f"end_{d+1}") for d in range(days_total)]

    opt = Optimize()

    # Domain: city indices
    for d in range(days_total):
        opt.add(And(Start[d] >= 0, Start[d] < len(cities)))
        opt.add(And(End[d] >= 0, End[d] < len(cities)))

    # Continuity: end of day d equals start of day d+1
    for d in range(days_total - 1):
        opt.add(Start[d + 1] == End[d])

    # Flights must be direct or stay put
    def flight_ok(d):
        same = Start[d] == End[d]
        allowed = Or(*[And(Start[d] == a, End[d] == b) for (a, b) in adj]) if adj else False
        return Or(same, allowed)

    for d in range(days_total):
        opt.add(flight_ok(d))

    # Presence booleans per day per city
    present = [[Bool(f"present_d{d+1}_c{c}") for c in range(len(cities))] for d in range(days_total)]
    for d in range(days_total):
        for c in range(len(cities)):
            opt.add(present[d][c] == Or(Start[d] == c, End[d] == c))

    # Totals per city
    totals = {}
    for c in range(len(cities)):
        totals[c] = Sum([If(present[d][c], 1, 0) for d in range(days_total)])

    # Must visit all six cities at least one day
    for c in range(len(cities)):
        opt.add(totals[c] >= 1)

    # Event windows (hard constraints):
    # Munich show: Day 4-8 inclusive => must be present in Munich on each of these days
    for day in range(4, 9):  # 1-based
        d = day - 1
        opt.add(Or(Start[d] == MUNICH, End[d] == MUNICH))

    # Wedding in Milan between Day 11 and Day 13: must be in Milan at least one of those days
    milan_window_days = [11, 12, 13]
    opt.add(Or([Or(Start[d-1] == MILAN, End[d-1] == MILAN) for d in milan_window_days]))

    # Meet friends in Krakow between Day 8 and Day 9: must be in Krakow at least one of those days
    krakow_window_days = [8, 9]
    opt.add(Or([Or(Start[d-1] == KRAKOW, End[d-1] == KRAKOW) for d in krakow_window_days]))

    # Objective: minimize deviation from desired durations + encourage presence on key days
    dev_vars = []
    for c in range(len(cities)):
        dev = Int(f"dev_{c}")
        opt.add(dev >= 0)
        opt.add(dev >= totals[c] - targets[c])
        opt.add(dev >= targets[c] - totals[c])
        dev_vars.append((weights[c], dev))

    # Encourage 3 full days in Milan during the wedding window (soft)
    milan_soft_penalties = []
    for d in milan_window_days:
        idx = d - 1
        miss = Int(f"miss_milan_day_{d}")
        opt.add(miss == If(Or(Start[idx] == MILAN, End[idx] == MILAN), 0, 1))
        milan_soft_penalties.append(miss)

    # Encourage presence in Krakow on both Day 8 and Day 9 (soft)
    krakow_soft_penalties = []
    for d in krakow_window_days:
        idx = d - 1
        miss = Int(f"miss_krakow_day_{d}")
        opt.add(miss == If(Or(Start[idx] == KRAKOW, End[idx] == KRAKOW), 0, 1))
        krakow_soft_penalties.append(miss)

    # Optional: mild penalty for number of flight days to avoid excessive hopping
    flight_days = []
    for d in range(days_total):
        f = Int(f"flight_day_{d+1}")
        opt.add(f == If(Start[d] != End[d], 1, 0))
        flight_days.append(f)

    # Total objective
    total_deviation = Sum([w * dev for (w, dev) in dev_vars])
    milan_window_penalty = 3 * Sum(milan_soft_penalties)   # weight 3 per missed Milan day in the wedding window
    krakow_window_penalty = 3 * Sum(krakow_soft_penalties) # weight 3 per missed Krakow day in the friends window
    flight_penalty = 1 * Sum(flight_days)                  # small penalty for each flight day

    objective = total_deviation + milan_window_penalty + krakow_window_penalty + flight_penalty
    opt.minimize(objective)

    # Solve
    if opt.check() != sat:
        # Fallback: unsat (should not happen with soft objectives)
        return {"itinerary": []}

    model = opt.model()

    # Extract end-city per day and build contiguous segments
    end_cities = [model.evaluate(End[d]).as_long() for d in range(days_total)]

    itinerary_segments = []
    seg_start = 1
    current_city = end_cities[0]
    for day in range(2, days_total + 1):
        if end_cities[day - 1] != current_city:
            itinerary_segments.append({
                "day_range": f"Day {seg_start}-{day-1}",
                "place": cities[current_city]
            })
            seg_start = day
            current_city = end_cities[day - 1]
    itinerary_segments.append({
        "day_range": f"Day {seg_start}-{days_total}",
        "place": cities[current_city]
    })

    return {"itinerary": itinerary_segments}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))