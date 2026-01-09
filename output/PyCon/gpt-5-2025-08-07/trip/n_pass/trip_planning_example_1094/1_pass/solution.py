import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input parameters
    cities = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
    presence_targets = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2,
    }
    total_days = 16

    # Special day constraints (inclusive ranges)
    paris_wedding_days = [1, 2]  # must be in Paris on days 1 and 2
    hamburg_conference_days = [10, 11]  # must be in Hamburg on days 10 and 11
    edinburgh_friend_window = [12, 13, 14, 15]  # at least one of these days in Edinburgh
    stockholm_relatives_days = [15, 16]  # must be in Stockholm on days 15 and 16

    # Flight network: build directed edges set
    undirected_pairs = [
        ("Hamburg", "Stockholm"),
        ("Vienna", "Stockholm"),
        ("Paris", "Edinburgh"),
        ("Riga", "Barcelona"),
        ("Paris", "Riga"),
        ("Krakow", "Barcelona"),
        ("Edinburgh", "Stockholm"),
        ("Paris", "Krakow"),
        ("Krakow", "Stockholm"),
        ("Riga", "Edinburgh"),
        ("Barcelona", "Stockholm"),
        ("Paris", "Stockholm"),
        ("Krakow", "Edinburgh"),
        ("Vienna", "Hamburg"),
        ("Paris", "Hamburg"),
        ("Riga", "Stockholm"),
        ("Hamburg", "Barcelona"),
        ("Vienna", "Barcelona"),
        ("Krakow", "Vienna"),
        ("Barcelona", "Edinburgh"),
        ("Paris", "Barcelona"),
        ("Hamburg", "Edinburgh"),
        ("Paris", "Vienna"),
        ("Vienna", "Riga"),
    ]
    directed_only = [
        ("Riga", "Hamburg"),  # one-way as per input
    ]

    edges = set()
    for a, b in undirected_pairs:
        edges.add((a, b))
        edges.add((b, a))
    for a, b in directed_only:
        edges.add((a, b))

    # Constraint solver setup
    problem = Problem()
    segment_vars = [f"seg{i}" for i in range(1, 9)]
    for var in segment_vars:
        problem.addVariable(var, cities)

    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), segment_vars)

    # Custom global constraint to enforce sequence, durations, presence, and flight feasibility
    def itinerary_constraint(*order_tuple):
        order = list(order_tuple)
        # Validate adjacency flights
        for i in range(len(order) - 1):
            if (order[i], order[i + 1]) not in edges:
                return False

        last_city = order[-1]

        # Compute segment lengths: L(city) = presence - 1 if not last; last gets full presence
        L = {}
        for c in cities:
            if c == last_city:
                L[c] = presence_targets[c]
            else:
                L[c] = presence_targets[c] - 1
            if L[c] <= 0:
                return False

        # Build schedule blocks (end-of-day city for each segment)
        start_day = 1
        day_blocks = {}  # city -> (start, end) inclusive end-of-day days
        for c in order:
            end_day = start_day + L[c] - 1
            day_blocks[c] = (start_day, end_day)
            start_day = end_day + 1

        # Ensure exactly total_days are covered by the segments
        if day_blocks[last_city][1] != total_days:
            return False

        # Compute presence days per city, counting departure day for non-last cities
        presence_days = {c: set() for c in cities}
        for idx, c in enumerate(order):
            s, e = day_blocks[c]
            presence_days[c].update(range(s, e + 1))
            if c != last_city:
                # departure on day e+1 counts for this city too
                presence_days[c].add(e + 1)

        # Validate presence counts match targets
        for c in cities:
            if len(presence_days[c]) != presence_targets[c]:
                return False

        # Special day constraints
        # Paris days 1 and 2 must be present
        if not all(d in presence_days["Paris"] for d in paris_wedding_days):
            return False

        # Hamburg conference days 10 and 11
        if not all(d in presence_days["Hamburg"] for d in hamburg_conference_days):
            return False

        # At least one Edinburgh day in [12..15]
        if not any(d in presence_days["Edinburgh"] for d in edinburgh_friend_window):
            return False

        # Stockholm on days 15 and 16
        if not all(d in presence_days["Stockholm"] for d in stockholm_relatives_days):
            return False

        return True

    problem.addConstraint(itinerary_constraint, segment_vars)

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build ordered list
    order = [solution[f"seg{i}"] for i in range(1, 9)]
    last_city = order[-1]
    # Compute lengths again to produce itinerary
    L = {c: (presence_targets[c] if c == last_city else presence_targets[c] - 1) for c in cities}

    # Compute day blocks
    start_day = 1
    itinerary = []
    for c in order:
        end_day = start_day + L[c] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": c
        })
        start_day = end_day + 1

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()