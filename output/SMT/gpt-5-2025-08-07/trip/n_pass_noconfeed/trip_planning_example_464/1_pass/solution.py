import json
from z3 import *

def main():
    # Parameters (input variables)
    total_days = 18
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    city_index = {c: i for i, c in enumerate(cities)}
    # Required city-day counts
    required_days = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5,
    }
    # Time windows: must be in Dubrovnik on some day in 5..9; in Oslo on some day in 16..18
    window_constraints = {
        "Dubrovnik": (5, 9),
        "Oslo": (16, 18),
    }
    # Direct flight graph (bidirectional pairs)
    direct_pairs = set()
    def add_edge(a, b):
        direct_pairs.add((city_index[a], city_index[b]))
        direct_pairs.add((city_index[b], city_index[a]))
    add_edge("Dubrovnik", "Oslo")
    add_edge("Frankfurt", "Krakow")
    add_edge("Frankfurt", "Oslo")
    add_edge("Dubrovnik", "Frankfurt")
    add_edge("Krakow", "Oslo")
    add_edge("Naples", "Oslo")
    add_edge("Naples", "Dubrovnik")
    add_edge("Naples", "Frankfurt")

    # Z3 setup
    D = total_days
    C = len(cities)
    opt = Optimize()

    # Variables:
    # loc[d] = end-of-day location index on day d (0..C-1). Also define loc_0 as start-of-day for day 1.
    loc = [Int(f"loc_{d}") for d in range(0, D+1)]
    for d in range(0, D+1):
        opt.add(And(loc[d] >= 0, loc[d] < C))

    # Flight variables for each day: at most one flight per day
    fly = [Bool(f"fly_{d}") for d in range(1, D+1)]
    frm = [Int(f"from_{d}") for d in range(1, D+1)]
    to = [Int(f"to_{d}") for d in range(1, D+1)]
    for d in range(1, D+1):
        opt.add(And(frm[d-1] >= 0, frm[d-1] < C))
        opt.add(And(to[d-1] >= 0, to[d-1] < C))
        # If flight occurs, it must be a direct flight from loc[d-1] to loc[d]
        allowed_disj = Or([And(frm[d-1] == i, to[d-1] == j) for (i, j) in direct_pairs]) if direct_pairs else False
        opt.add(Implies(fly[d-1], And(
            frm[d-1] != to[d-1],
            allowed_disj,
            loc[d-1] == frm[d-1],
            loc[d] == to[d-1]
        )))
        # If no flight, location stays the same
        opt.add(Implies(Not(fly[d-1]), loc[d] == loc[d-1]))

    # In[c][d]: true iff on day d we are counted in city c (flight-day counts both endpoints)
    In = [[Bool(f"in_{c}_{d}") for d in range(1, D+1)] for c in range(C)]
    for d in range(1, D+1):
        for c in range(C):
            opt.add(In[c][d-1] == Or(
                And(Not(fly[d-1]), loc[d] == c),
                And(fly[d-1], Or(frm[d-1] == c, to[d-1] == c))
            ))

    # City day totals
    for city, req in required_days.items():
        idx = city_index[city]
        opt.add(Sum([If(In[idx][d-1], 1, 0) for d in range(1, D+1)]) == req)

    # Window constraints
    # Dubrovnik between day 5 and 9
    dub_idx = city_index["Dubrovnik"]
    dub_w = window_constraints["Dubrovnik"]
    opt.add(Or([In[dub_idx][d-1] for d in range(dub_w[0], dub_w[1] + 1)]))
    # Oslo between day 16 and 18
    osl_idx = city_index["Oslo"]
    osl_w = window_constraints["Oslo"]
    opt.add(Or([In[osl_idx][d-1] for d in range(osl_w[0], osl_w[1] + 1)]))

    # Optional consistency check: sum of all city-day counts equals 18 + number_of_flights
    flights_count = Sum([If(fly[d-1], 1, 0) for d in range(1, D+1)])
    total_city_days = Sum([
        If(In[c][d-1], 1, 0)
        for c in range(C)
        for d in range(1, D+1)
    ])
    opt.add(total_city_days == total_days + flights_count)

    # Optimization: minimize number of flights
    opt.minimize(flights_count)

    # Solve
    if opt.check() != sat:
        # In the unlikely case it's unsat (should not be), return empty itinerary
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    def is_true_val(b):  # helper to interpret BoolRef
        return is_true(m.evaluate(b, model_completion=True))

    # Build day-by-day labels; on flight day show "A & B", else "A"
    per_day_labels = []
    for d in range(1, D+1):
        if is_true_val(fly[d-1]):
            f_idx = m.evaluate(frm[d-1], model_completion=True).as_long()
            t_idx = m.evaluate(to[d-1], model_completion=True).as_long()
            label = f"{cities[f_idx]} & {cities[t_idx]}"
        else:
            l_idx = m.evaluate(loc[d], model_completion=True).as_long()
            label = cities[l_idx]
        per_day_labels.append(label)

    # Compress consecutive days with same label into ranges
    itinerary = []
    start = 1
    current_label = per_day_labels[0]
    for d in range(2, D+1):
        if per_day_labels[d-1] != current_label:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}",
                "place": current_label
            })
            start = d
            current_label = per_day_labels[d-1]
    # Last segment
    itinerary.append({
        "day_range": f"Day {start}-{D}",
        "place": current_label
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()