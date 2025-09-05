import json
from itertools import permutations

def build_directed_edges():
    edges = set()
    # Bidirectional edges
    bidir = [
        ("Helsinki", "Riga"),
        ("Vienna", "Helsinki"),
        ("Riga", "Dublin"),
        ("Vienna", "Riga"),
        ("Reykjavik", "Vienna"),
        ("Helsinki", "Dublin"),
        ("Tallinn", "Dublin"),
        ("Reykjavik", "Helsinki"),
        ("Reykjavik", "Dublin"),
        ("Helsinki", "Tallinn"),
        ("Vienna", "Dublin"),
    ]
    for a, b in bidir:
        edges.add((a, b))
        edges.add((b, a))
    # Directed edges
    edges.add(("Riga", "Tallinn"))  # from Riga to Tallinn only
    return edges

def build_schedule(order, durations, total_days):
    n = len(order)
    # Calculate labeled days per city (days assigned to that city in the output)
    labeled_days = {}
    for i, city in enumerate(order):
        dur = durations[city]
        if i == 0:  # first city
            labeled_days[city] = dur - 1
        elif i == n - 1:  # last city
            labeled_days[city] = dur
        else:  # interior city
            labeled_days[city] = dur - 1
        if labeled_days[city] < 0:
            return None  # infeasible

    # Create day-by-day labeled itinerary and track flight days
    days = []
    flights = []  # list of tuples (day, origin, destination)
    # Place first city's labeled days (no arrival flight day exists for the first)
    first_city = order[0]
    for _ in range(labeled_days[first_city]):
        days.append(first_city)

    # For each transition, add the flight day (labeled as destination) then the remaining labeled days of destination
    for i in range(n - 1):
        origin = order[i]
        dest = order[i + 1]
        # Flight day
        days.append(dest)
        flights.append((len(days), origin, dest))  # day index is 1-based
        # Remaining labeled days for destination (we already placed 1 labeled day for dest)
        remaining = labeled_days[dest] - 1
        for _ in range(max(0, remaining)):
            days.append(dest)

    if len(days) != total_days:
        return None

    # Compute presence counts per city considering flight-day double counting
    presence = {city: set() for city in order}
    # Add labeled presence
    for idx, city in enumerate(days, start=1):
        presence[city].add(idx)
    # Add origin presence on flight days
    for day_idx, origin, dest in flights:
        presence[origin].add(day_idx)

    # Verify durations match exactly
    for city in order:
        if len(presence[city]) != durations[city]:
            return None

    return days, flights, presence

def verify_constraints(order, days, presence, flights, constraints):
    # 1) Only direct flights between consecutive cities
    edges = constraints["edges"]
    for i in range(len(order) - 1):
        if (order[i], order[i+1]) not in edges:
            return False

    # 2) Time window constraints
    # Vienna show on days 2 and 3
    vienna_days = presence["Vienna"]
    if not ({2, 3}.issubset(vienna_days)):
        return False

    # Helsinki meet between day 3 and 5 (at least one day)
    hel_days = presence["Helsinki"]
    if len(hel_days.intersection({3, 4, 5})) == 0:
        return False

    # Tallinn wedding between day 7 and 11 (at least one day)
    tal_days = presence["Tallinn"]
    if len(tal_days.intersection(set(range(7, 12)))) == 0:
        return False

    # 3) City stay durations already enforced in build_schedule

    return True

def compress_itinerary(days):
    # Compress consecutive identical entries into ranges
    itinerary = []
    if not days:
        return itinerary
    start = 1
    current = days[0]
    for i in range(1, len(days)):
        if days[i] != current:
            itinerary.append({"day_range": f"Day {start}-{i}", "place": current})
            start = i + 1
            current = days[i]
    itinerary.append({"day_range": f"Day {start}-{len(days)}", "place": current})
    return itinerary

def main():
    # Input variables (constraints)
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    durations = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5,
    }
    total_days = 15

    edges = build_directed_edges()

    constraints = {
        "edges": edges,
        "total_days": total_days,
        "durations": durations,
    }

    # Search for a valid city order and schedule
    best_result = None
    # Heuristic: Vienna likely needs to be 2nd to cover days 2-3; Reykjavik (2-day city) likely 1st.
    # We'll prioritize permutations with Reykjavik first and Vienna second, but still fall back to all permutations if needed.
    prioritized_orders = []
    rest_orders = []
    for order in permutations(cities):
        if len(set(order)) != len(cities):
            continue
        if order[1] == "Vienna" and order[0] == "Reykjavik":
            prioritized_orders.append(order)
        else:
            rest_orders.append(order)

    for orders_to_try in (prioritized_orders, rest_orders):
        for order in orders_to_try:
            # Build schedule
            built = build_schedule(order, durations, total_days)
            if not built:
                continue
            days, flights, presence = built
            # Verify all constraints including direct flights and time windows
            if verify_constraints(order, days, presence, flights, constraints):
                best_result = days
                break
        if best_result:
            break

    if not best_result:
        # If no valid plan found, output empty itinerary
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Compress into ranges for output
    itinerary = compress_itinerary(best_result)
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()