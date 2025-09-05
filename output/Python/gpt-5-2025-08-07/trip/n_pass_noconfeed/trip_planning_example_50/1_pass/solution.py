import json
import itertools

def compute_itinerary(cities_with_days, total_days, direct_flights):
    """
    cities_with_days: list of tuples (city_name, desired_days)
    total_days: total trip length (calendar days)
    direct_flights: set of directed edges (origin, destination) that are direct flights
    """
    city_names = [c for c, _ in cities_with_days]
    desired_days_map = {c: d for c, d in cities_with_days}
    k = len(city_names)

    # Helper to check if a route is valid w.r.t direct flights
    def is_direct_route(order):
        return all((order[i], order[i+1]) in direct_flights for i in range(len(order)-1))

    # For a given order, verify the total length matches when counting overlaps on flight days
    def valid_length_for_order(order):
        s = sum(desired_days_map[c] for c in order)
        # With K cities visited once sequentially, there are K-1 flights (overlap days)
        return s - (len(order) - 1)

    # Try all permutations; pick the first that satisfies direct-flight constraints and length
    for order in itertools.permutations(city_names):
        if not is_direct_route(order):
            continue
        calc_total = valid_length_for_order(order)
        if calc_total != total_days:
            continue

        # Compute day ranges with overlaps on flight days:
        # end_day_i = sum(d1..di) - (i-1); start_day_1=1; start_day_i = end_day_{i-1} for i>1
        itinerary = []
        running_sum = 0
        for i, city in enumerate(order, start=1):
            running_sum += desired_days_map[city]
            end_day = running_sum - (i - 1)
            if i == 1:
                start_day = 1
            else:
                # Overlap on flight day with previous city
                prev_end_day = itinerary[-1]["_end_day_internal"]
                start_day = prev_end_day
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city,
                "_end_day_internal": end_day  # internal helper to compute overlaps
            })

        # Clean internal fields
        for item in itinerary:
            item.pop("_end_day_internal", None)

        return {"itinerary": itinerary}

    # If no valid plan found
    return {"itinerary": []}

if __name__ == "__main__":
    # Input parameters based on the problem statement
    cities_with_days = [
        ("Vilnius", 4),
        ("Munich", 3),
        ("Mykonos", 7)
    ]
    total_days = 12

    # Direct flights:
    # - Munich <-> Mykonos (both directions)
    # - Vilnius -> Munich (one way)
    direct_flights = {
        ("Munich", "Mykonos"),
        ("Mykonos", "Munich"),
        ("Vilnius", "Munich"),
    }

    result = compute_itinerary(cities_with_days, total_days, direct_flights)
    print(json.dumps(result))