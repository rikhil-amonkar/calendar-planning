import json
import itertools

def compute_itinerary(total_days, city_order, required_days, direct_pairs, must_be_in_city_days):
    # Build bidirectional adjacency for direct flights
    adj = set()
    for a, b in direct_pairs:
        adj.add((a, b))
        adj.add((b, a))

    # Validate input cities
    cities = list(required_days.keys())
    if set(cities) != set(city_order):
        raise ValueError("City order must include exactly the cities with required days.")

    # Validate direct flight path between consecutive cities in the chosen order
    for i in range(len(city_order) - 1):
        if (city_order[i], city_order[i + 1]) not in adj:
            raise ValueError(f"No direct flight between {city_order[i]} and {city_order[i+1]}")

    # Sum of "city-days" and number of flights required
    sum_required = sum(required_days[c] for c in city_order)
    required_flights = sum_required - total_days
    if required_flights < 0:
        raise ValueError("Sum of required city-days cannot be less than total days.")
    if required_flights != len(city_order) - 1:
        raise ValueError("Given requirements imply a different number of flight days than the city sequence supports.")

    # Determine start city and ensure presence constraints
    start_city = city_order[0]
    presence_days = must_be_in_city_days.get(start_city, [])
    last_required_presence_day = max(presence_days) if presence_days else 0

    # Flight day from first to second city must ensure:
    # - Being in start city on all required presence days
    # - Exact day count in start city including the flight day
    r1 = required_days[start_city]
    if r1 < last_required_presence_day:
        raise ValueError("Required days in start city are less than forced presence days.")
    flight1_day = r1  # Depart on the r1-th day; counts towards start city and next city

    # Compute second flight day to satisfy middle city's required days
    middle_city = city_order[1]
    r2 = required_days[middle_city]
    flight2_day = flight1_day + r2 - 1  # Includes both flight days for the middle city

    # Validate end city's required days consistency
    end_city = city_order[2]
    r3_expected = total_days - flight2_day + 1
    if r3_expected != required_days[end_city]:
        raise ValueError("End city's required days do not align with computed schedule.")

    if not (1 <= flight1_day < flight2_day <= total_days):
        raise ValueError("Computed flight days are out of bounds or not in increasing order.")

    # Build itinerary with overlapping ranges on flight days
    itinerary = [
        {"day_range": f"Day 1-{flight1_day}", "place": start_city},
        {"day_range": f"Day {flight1_day}-{flight2_day}", "place": middle_city},
        {"day_range": f"Day {flight2_day}-{total_days}", "place": end_city},
    ]

    return itinerary

if __name__ == "__main__":
    # Input variables as per the user's constraints
    total_days = 12
    required_days = {
        "Brussels": 2,
        "Barcelona": 7,
        "Split": 5
    }
    # Direct flights available (undirected)
    direct_pairs = [
        ("Brussels", "Barcelona"),
        ("Barcelona", "Split")
    ]
    # Mandatory presence: Day 1 and Day 2 in Brussels (conference)
    must_be_in_city_days = {
        "Brussels": [1, 2]
    }
    # Determine a valid city order starting in Brussels using available direct flights
    cities = list(required_days.keys())
    start_city = "Brussels"

    valid_orders = []
    for perm in itertools.permutations(cities):
        if perm[0] != start_city:
            continue
        # Check direct edges between consecutive cities
        ok = True
        adj = set()
        for a, b in direct_pairs:
            adj.add((a, b))
            adj.add((b, a))
        for i in range(len(perm) - 1):
            if (perm[i], perm[i + 1]) not in adj:
                ok = False
                break
        if ok:
            valid_orders.append(list(perm))

    # Choose an order that matches the required number of flights (sum_required - total_days)
    sum_required = sum(required_days.values())
    required_flights = sum_required - total_days
    chosen_order = None
    for order in valid_orders:
        if len(order) - 1 == required_flights:
            chosen_order = order
            break

    if not chosen_order:
        raise RuntimeError("No valid city order found that matches the direct flights and flight-day requirements.")

    itinerary = compute_itinerary(
        total_days=total_days,
        city_order=chosen_order,
        required_days=required_days,
        direct_pairs=direct_pairs,
        must_be_in_city_days=must_be_in_city_days
    )

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))