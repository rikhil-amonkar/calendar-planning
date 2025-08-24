import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 10
    planned_stays = {
        "London": 3,
        "Santorini": 6,
        "Istanbul": 3
    }
    must_be_in_city_on_days = {
        "Santorini": [5, 10]  # Must attend conference on Day 5 and Day 10 in Santorini
    }
    # Direct flights (undirected)
    direct_flights = {("Istanbul", "London"), ("London", "Santorini")}
    cities = list(planned_stays.keys())

    def is_direct(a, b):
        return (a, b) in direct_flights or (b, a) in direct_flights

    # Feasibility relationship: total extra city-days created by flights equals number of flights
    # With contiguous segments across k cities, flights = k - 1
    flights_needed = sum(planned_stays.values()) - total_days
    transitions_required = len(cities) - 1
    if flights_needed != transitions_required:
        raise ValueError("No solution under exact-day constraints with given flights and total days.")

    # If a city must be on the last day, prioritize permutations ending with that city
    must_on_last_day = None
    for city, days in must_be_in_city_on_days.items():
        if total_days in days:
            must_on_last_day = city
            break

    # Generate candidate city orders (permutations) that respect direct flights and last-day constraint
    candidate_orders = []
    for perm in itertools.permutations(cities):
        if not (is_direct(perm[0], perm[1]) and is_direct(perm[1], perm[2])):
            continue
        if must_on_last_day and perm[-1] != must_on_last_day:
            continue
        candidate_orders.append(perm)

    def day_belongs_to_city(day, f1, f2, order):
        # Segments:
        # City1: Day 1 ... f1
        # City2: Day f1 ... f2
        # City3: Day f2 ... total_days
        belongs = set()
        if 1 <= day <= f1:
            belongs.add(order[0])
        if f1 <= day <= f2:
            belongs.add(order[1])
        if f2 <= day <= total_days:
            belongs.add(order[2])
        return belongs

    def build_itinerary(order, f1, f2):
        # Build day ranges that include overlapping transition days
        segments = [
            {"day_range": f"Day 1-{f1}", "place": order[0]},
            {"day_range": f"Day {f1}-{f2}", "place": order[1]},
            {"day_range": f"Day {f2}-{total_days}", "place": order[2]},
        ]
        return segments

    # Try to find a valid order and flight days
    for order in candidate_orders:
        c1 = planned_stays[order[0]]
        c2 = planned_stays[order[1]]
        c3 = planned_stays[order[2]]

        # For contiguous segments, flight days are pinned by planned stays:
        # f1 = c1 (first flight day), f2 = c1 + c2 - 1 (second flight day)
        f1 = c1
        f2 = c1 + c2 - 1

        # Check bounds
        if not (1 <= f1 <= f2 <= total_days):
            continue

        # Check c3 consistency: last segment length should be c3
        if (total_days - f2 + 1) != c3:
            continue

        # Validate must-be-in-city days
        valid = True
        for city, days in must_be_in_city_on_days.items():
            for d in days:
                if city not in day_belongs_to_city(d, f1, f2, order):
                    valid = False
                    break
            if not valid:
                break
        if not valid:
            continue

        # Found a valid itinerary
        itinerary = build_itinerary(order, f1, f2)
        return {"itinerary": itinerary}

    raise ValueError("No valid itinerary found with the given constraints.")

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))