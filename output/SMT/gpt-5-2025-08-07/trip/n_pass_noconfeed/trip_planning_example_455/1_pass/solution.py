import json
from z3 import *

def main():
    # Trip parameters
    total_days = 21
    cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
    city_index = {name: i for i, name in enumerate(cities)}

    # Duration constraints (total days in each city, including flight overlap as specified)
    required_days = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7,
    }

    # Direct flight adjacency (undirected)
    direct_flights = {
        ("Istanbul", "Krakow"),
        ("Warsaw", "Reykjavik"),
        ("Istanbul", "Warsaw"),
        ("Riga", "Istanbul"),
        ("Krakow", "Warsaw"),
        ("Riga", "Warsaw"),
    }
    # Make adjacency oriented pairs
    oriented_pairs = set()
    for a, b in direct_flights:
        oriented_pairs.add((city_index[a], city_index[b]))
        oriented_pairs.add((city_index[b], city_index[a]))

    # Helper function to build adjacency constraint
    def direct_adj_constraint(prev_var, curr_var):
        return Or(*[And(prev_var == a, curr_var == b) for (a, b) in oriented_pairs])

    # SMT variables
    N = total_days
    num_cities = len(cities)

    city_vars = [Int(f"city_{d}") for d in range(1, N + 1)]
    flight_day = [Bool(f"flight_day_{d}") if d >= 2 else None for d in range(1, N + 1)]

    opt = Optimize()

    # Domain constraints for city variables
    for v in city_vars:
        opt.add(And(v >= 0, v < num_cities))

    # Flight and adjacency constraints
    for d in range(1, N):
        prev_v = city_vars[d - 1]
        curr_v = city_vars[d]
        # flight occurs if city changes
        opt.add(flight_day[d + 1 - 1] == (prev_v != curr_v))  # indexing: flight_day[d] corresponds to day d+1, but using 0-based list
        # if flight occurs, must be direct
        opt.add(Implies(prev_v != curr_v, direct_adj_constraint(prev_v, curr_v)))

    # Each required city must appear at least once in base assignment
    for cname in cities:
        c = city_index[cname]
        opt.add(Or([city_vars[d] == c for d in range(N)]))

    # Total days per city accounting for flight overlap rule:
    # If one flies from city A to city B on day X (i.e., city changes between X-1 and X), then day X counts for both A and B.
    # Our representation: if city[d] != city[d-1], then flight_day[d] is true, and day d counts:
    # - as a base day for city[d]
    # - as an extra (bonus) day for city[d-1]
    totals = {}
    for cname in cities:
        c = city_index[cname]
        base = Sum([If(city_vars[d] == c, 1, 0) for d in range(N)])
        bonus_terms = []
        for d in range(1, N):  # day index d corresponds to day d+1 (1-based)
            # flight_day at day (d+1) is flight_day[d] in list (0-based)
            bonus_terms.append(If(And(flight_day[d], city_vars[d - 1] == c), 1, 0))
        bonus = Sum(bonus_terms) if bonus_terms else IntVal(0)
        totals[cname] = base + bonus
        opt.add(totals[cname] == required_days[cname])

    # Meeting friend in Riga between day 1 and day 2 (inclusive)
    riga = city_index["Riga"]
    # presence on day d: city[d] == c OR (d>1 and flight_day[d] and city[d-1]==c)
    def presence_on_day(c, d1_based):
        d = d1_based - 1
        if d1_based == 1:
            return city_vars[d] == c
        else:
            return Or(city_vars[d] == c, And(flight_day[d], city_vars[d - 1] == c))

    opt.add(Or(presence_on_day(riga, 1), presence_on_day(riga, 2)))

    # Wedding in Istanbul between day 2 and day 7 (inclusive)
    istanbul = city_index["Istanbul"]
    opt.add(Or([presence_on_day(istanbul, d) for d in range(2, 8)]))

    # Only 5 specific cities are allowed; already enforced by domain and days per city constraints.

    # Minimize the number of flights (to find the simplest feasible plan)
    total_flights = Sum([If(flight_day[d], 1, 0) for d in range(1, N)])
    opt.minimize(total_flights)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return
    m = opt.model()

    # Extract day-by-day base city assignment
    day_cities = [m.evaluate(city_vars[d]).as_long() for d in range(N)]

    # Build contiguous segments by base assignment. Flight days are the first day of the new segment.
    itinerary = []
    start_day = 1
    curr_city = day_cities[0]
    for d in range(2, N + 1):
        if day_cities[d - 1] != curr_city:
            end_day = d - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[curr_city]
            })
            start_day = d
            curr_city = day_cities[d - 1]
    # Add final segment
    itinerary.append({
        "day_range": f"Day {start_day}-{N}",
        "place": cities[curr_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()