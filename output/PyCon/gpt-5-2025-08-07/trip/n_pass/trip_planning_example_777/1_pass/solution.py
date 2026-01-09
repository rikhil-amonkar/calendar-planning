import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 15
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    required_days = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5,
    }

    # Direct flight pairs (treated as undirected)
    direct_pairs = {
        frozenset(("Helsinki", "Riga")),
        frozenset(("Riga", "Tallinn")),
        frozenset(("Vienna", "Helsinki")),
        frozenset(("Riga", "Dublin")),
        frozenset(("Vienna", "Riga")),
        frozenset(("Reykjavik", "Vienna")),
        frozenset(("Helsinki", "Dublin")),
        frozenset(("Tallinn", "Dublin")),
        frozenset(("Reykjavik", "Helsinki")),
        frozenset(("Reykjavik", "Dublin")),
        frozenset(("Helsinki", "Tallinn")),
        frozenset(("Vienna", "Dublin")),
    }

    def is_direct(a, b):
        return frozenset((a, b)) in direct_pairs

    # Build the per-day destination list and presence per day given an order
    def build_schedule(order):
        # Order is a list of 6 distinct cities (visit sequence)
        # Derive destination-day sequence based on required_days:
        # For city k in order (1-based):
        #  - k == 1: add r[city] - 1 destination days
        #  - 2 <= k <= 5: add 1 arrival day + (r[city] - 2) stay days
        #  - k == 6: add 1 arrival day + (r[city] - 1) stay days
        dest_list = []
        # First city
        first = order[0]
        dest_list += [first] * (required_days[first] - 1)
        # Middle cities
        for city in order[1:5]:
            dest_list.append(city)  # arrival/flight day
            add_stays = required_days[city] - 2
            if add_stays > 0:
                dest_list += [city] * add_stays
        # Last city
        last = order[5]
        dest_list.append(last)  # arrival/flight day
        add_stays_last = required_days[last] - 1
        if add_stays_last > 0:
            dest_list += [last] * add_stays_last

        assert len(dest_list) == total_days, f"Internal schedule error: {len(dest_list)} days"

        # Presence per day: on change days, both previous and current city count
        presence = {}
        for d in range(1, total_days + 1):
            if d == 1:
                presence[d] = {dest_list[0]}
            else:
                prev_city = dest_list[d - 2]
                curr_city = dest_list[d - 1]
                if prev_city != curr_city:
                    presence[d] = {prev_city, curr_city}
                else:
                    presence[d] = {curr_city}
        return dest_list, presence

    # Create CSP
    problem = Problem()

    # Variables for order positions 1..6
    pos_vars = [f"pos{i}" for i in range(1, 7)]
    for var in pos_vars:
        problem.addVariable(var, cities)

    # All cities visited exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Adjacency (direct flights) between consecutive cities in the order
    for i in range(1, 6):
        def make_adj(i=i):
            def adj_constraint(a, b):
                return is_direct(a, b)
            return adj_constraint
        problem.addConstraint(make_adj(), (f"pos{i}", f"pos{i+1}"))

    # Global constraint to satisfy event windows and city-day totals implicitly
    def global_event_constraint(*order_tuple):
        order = list(order_tuple)

        # Build schedule from the order
        dest_list, presence = build_schedule(order)

        # Validate per-city total day counts (each day counts destination + origin on flight days)
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            for c in presence[d]:
                counts[c] += 1

        # Check required days per city
        for c in cities:
            if counts[c] != required_days[c]:
                return False

        # Event: Vienna show on Day 2 and Day 3 (must be present both days)
        if not ("Vienna" in presence[2] and "Vienna" in presence[3]):
            return False

        # Event: Meet friends in Helsinki between Day 3 and Day 5 (present at least one day in that window)
        if not any("Helsinki" in presence[d] for d in range(3, 6)):
            return False

        # Event: Wedding in Tallinn between Day 7 and Day 11 (present at least one day in that window)
        if not any("Tallinn" in presence[d] for d in range(7, 12)):
            return False

        return True

    problem.addConstraint(global_event_constraint, pos_vars)

    solution = problem.getSolution()
    if not solution:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    # Build the final schedule and aggregate into day ranges
    order = [solution[f"pos{i}"] for i in range(1, 7)]
    dest_list, presence = build_schedule(order)

    # Aggregate contiguous blocks by destination city for output
    itinerary = []
    start = 1
    current_city = dest_list[0]
    for day in range(2, total_days + 1):
        if dest_list[day - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{day - 1}",
                "place": current_city
            })
            start = day
            current_city = dest_list[day - 1]
    # Append last block
    itinerary.append({
        "day_range": f"Day {start}-{total_days}",
        "place": current_city
    })

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()