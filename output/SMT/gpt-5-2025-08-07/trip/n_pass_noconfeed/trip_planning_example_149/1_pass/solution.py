import json
from z3 import Int, Bool, Optimize, And, Or, Not, If, Sum

def solve_itinerary():
    # Input parameters
    days_total = 10
    cities = ["London", "Santorini", "Istanbul"]
    city_to_idx = {name: i for i, name in enumerate(cities)}
    idx_to_city = {i: name for i, name in enumerate(cities)}

    required_days = {
        "London": 3,
        "Santorini": 6,
        "Istanbul": 3,
    }
    conference_days = {
        "Santorini": [5, 10]
    }

    # Adjacency: only direct flights between Istanbul-London and London-Santorini
    def direct(u, v):
        return Or(
            And(u == city_to_idx["London"], v == city_to_idx["Santorini"]),
            And(u == city_to_idx["Santorini"], v == city_to_idx["London"]),
            And(u == city_to_idx["London"], v == city_to_idx["Istanbul"]),
            And(u == city_to_idx["Istanbul"], v == city_to_idx["London"]),
        )

    # Variables
    main = [Int(f"main_{d}") for d in range(1, days_total + 1)]  # main city each day (0..2)
    present = [[Bool(f"present_{c}_{d}") for d in range(1, days_total + 1)] for c in range(len(cities))]  # presence flags
    legs = [Int(f"legs_{d}") for d in range(1, days_total)]  # number of flight legs on day d (transitions from day d to d+1)

    opt = Optimize()

    # Domain constraints for main city variables
    for d in range(days_total):
        opt.add(And(main[d] >= 0, main[d] < len(cities)))

    # Presence and flight legs constraints
    transfer_city = city_to_idx["London"]  # only possible transfer city due to given direct flights

    for d in range(1, days_total + 1):
        # Determine change type between day d and d+1 (only if d < days_total)
        if d < days_total:
            u = main[d - 1]
            v = main[d]
            same = (u == v)
            is_direct_change = And(Not(same), direct(u, v))
            is_indirect_change = And(Not(same), Not(direct(u, v)))

            # Indirect changes are only allowed between Istanbul and Santorini via London
            opt.add(
                Or(
                    same,
                    is_direct_change,
                    And(
                        is_indirect_change,
                        Or(
                            And(u == city_to_idx["Istanbul"], v == city_to_idx["Santorini"]),
                            And(u == city_to_idx["Santorini"], v == city_to_idx["Istanbul"]),
                        )
                    )
                )
            )

            # Legs piecewise
            opt.add(
                legs[d - 1] == If(same, 0, If(direct(u, v), 1, 2))
            )

            # Presence equivalence for each city c on day d
            for c in range(len(cities)):
                # Base: in main city of day d
                base = (main[d - 1] == c)
                # Extra presence if direct change includes arrival city
                extra_direct = And(is_direct_change, v == c)
                # Extra presence if indirect change includes transfer city or arrival city
                extra_indirect = And(is_indirect_change, Or(c == transfer_city, v == c))
                opt.add(present[c][d - 1] == Or(base, extra_direct, extra_indirect))
        else:
            # Last day: no flights; presence only in main city
            for c in range(len(cities)):
                opt.add(present[c][d - 1] == (main[d - 1] == c))

    # Required presence counts per city
    for city_name, req_days in required_days.items():
        cidx = city_to_idx[city_name]
        opt.add(Sum([If(present[cidx][d], 1, 0) for d in range(days_total)]) == req_days)

    # Conference presence constraints
    for city_name, days in conference_days.items():
        cidx = city_to_idx[city_name]
        for d in days:
            # Days are 1-indexed
            opt.add(present[cidx][d - 1] == True)

    # Objective: minimize total number of flight legs
    total_legs = Sum(legs) if legs else 0
    opt.minimize(total_legs)

    # Solve
    if opt.check() !=  sat:
        # Fallback in case of unexpected unsat (should not happen with given constraints)
        return {"itinerary": []}

    model = opt.model()

    # Build itinerary by grouping contiguous days with the same main city
    main_vals = [model.evaluate(main[d]).as_long() for d in range(days_total)]

    itinerary = []
    start = 1
    current_city = main_vals[0]
    for day in range(2, days_total + 1):
        if main_vals[day - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{day - 1}",
                "place": idx_to_city[current_city]
            })
            start = day
            current_city = main_vals[day - 1]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start}-{days_total}",
        "place": idx_to_city[current_city]
    })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))