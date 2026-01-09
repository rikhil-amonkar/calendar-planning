import json
from constraint import Problem

def main():
    # Input variables and constraints
    TOTAL_DAYS = 11
    CITIES = ["Krakow", "Paris", "Seville"]
    REQUIRED_DAYS = {"Krakow": 5, "Paris": 2, "Seville": 6}
    WORKSHOP_CITY = "Krakow"
    WORKSHOP_WINDOW = (1, 5)  # inclusive window: must be in Krakow each day in this window
    DIRECT_FLIGHTS = {
        ("Krakow", "Paris"),
        ("Paris", "Krakow"),
        ("Paris", "Seville"),
        ("Seville", "Paris"),
    }

    # Derived inputs/checks
    # Sum of required days must equal TOTAL_DAYS + number_of_transitions (since flight days overlap)
    number_of_transitions = len(CITIES) - 1
    if sum(REQUIRED_DAYS[c] for c in CITIES) != TOTAL_DAYS + number_of_transitions:
        print(json.dumps({"itinerary": []}))
        return

    # We must pick an order that is achievable using only direct flights between consecutive cities.
    # Given direct flights graph, the only valid orders using all three distinct cities are:
    possible_city_orders = []
    for order in [
        ("Krakow", "Paris", "Seville"),
        ("Seville", "Paris", "Krakow"),
    ]:
        if (
            (order[0], order[1]) in DIRECT_FLIGHTS and
            (order[1], order[2]) in DIRECT_FLIGHTS and
            set(order) == set(CITIES)
        ):
            possible_city_orders.append(order)

    # Filter orders that can satisfy the workshop requirement: must be in WORKSHOP_CITY for the entire WORKSHOP_WINDOW.
    # With the travel model used below (contiguous segments, overlap on flight days),
    # the first city covers days 1..t1, so to cover the whole window [W1..W2] we need the WORKSHOP_CITY to be the first city
    # and t1 >= W2.
    feasible_orders = [order for order in possible_city_orders if order[0] == WORKSHOP_CITY]
    if not feasible_orders:
        print(json.dumps({"itinerary": []}))
        return

    # We'll attempt to solve for each feasible city order; pick the first with a solution.
    solution_itinerary = None

    for city_order in feasible_orders:
        c1, c2, c3 = city_order

        # Constraint problem:
        # Let t1 be the day we fly from c1 to c2 (inclusive for both cities)
        # Let t2 be the day we fly from c2 to c3 (inclusive for both cities)
        # Then:
        # - Days in c1 = t1
        # - Days in c2 = t2 - t1 + 1
        # - Days in c3 = TOTAL_DAYS - t2 + 1
        problem = Problem()
        problem.addVariable("t1", range(1, TOTAL_DAYS + 1))
        problem.addVariable("t2", range(1, TOTAL_DAYS + 1))

        # t1 < t2 within the trip window
        problem.addConstraint(lambda t1, t2: 1 <= t1 < t2 <= TOTAL_DAYS, ("t1", "t2"))

        # Durations must match required days
        def durations_match(t1, t2):
            d1 = t1
            d2 = t2 - t1 + 1
            d3 = TOTAL_DAYS - t2 + 1
            return (
                d1 == REQUIRED_DAYS[c1] and
                d2 == REQUIRED_DAYS[c2] and
                d3 == REQUIRED_DAYS[c3]
            )

        problem.addConstraint(durations_match, ("t1", "t2"))

        # Workshop constraint: be in WORKSHOP_CITY for every day in WORKSHOP_WINDOW.
        # With the first city covering days 1..t1, ensure t1 >= WORKSHOP_WINDOW[1]
        problem.addConstraint(lambda t1: t1 >= WORKSHOP_WINDOW[1], ("t1",))

        solutions = problem.getSolutions()
        if not solutions:
            continue

        # Choose a solution (e.g., earliest transitions)
        sol = sorted(solutions, key=lambda s: (s["t1"], s["t2"]))[0]
        t1, t2 = sol["t1"], sol["t2"]

        # Build itinerary with overlapping ranges on flight days
        itinerary = [
            {"day_range": f"Day 1-{t1}", "place": c1},
            {"day_range": f"Day {t1}-{t2}", "place": c2},
            {"day_range": f"Day {t2}-{TOTAL_DAYS}", "place": c3},
        ]

        # Final validation (safety check)
        # Count days-per-city with overlap rule
        # City presence:
        city_days = {c1: set(), c2: set(), c3: set()}
        for day in range(1, TOTAL_DAYS + 1):
            if 1 <= day <= t1:
                city_days[c1].add(day)
            if t1 <= day <= t2:
                city_days[c2].add(day)
            if t2 <= day <= TOTAL_DAYS:
                city_days[c3].add(day)

        valid = all(len(city_days[c]) == REQUIRED_DAYS[c] for c in CITIES)
        # Ensure workshop window is fully covered in WORKSHOP_CITY
        w1, w2 = WORKSHOP_WINDOW
        valid = valid and all(day in city_days[WORKSHOP_CITY] for day in range(w1, w2 + 1))

        if valid:
            solution_itinerary = itinerary
            break

    if solution_itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": solution_itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()