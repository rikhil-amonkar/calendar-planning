import itertools
import json

def compute_itinerary():
    # Input variables (constraints)
    total_days = 14
    city_durations = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3,
    }
    # Windows are inclusive: (start_day, end_day)
    city_windows = {
        "Amsterdam": (9, 11),  # must be in Amsterdam on days 9-11
        "Lyon": (7, 9),        # must be in Lyon on days 7-9
    }
    # Direct flights (bidirectional)
    direct_flights = {
        ("Vienna", "Lyon"),
        ("Vienna", "Santorini"),
        ("Vienna", "Amsterdam"),
        ("Amsterdam", "Santorini"),
        ("Lyon", "Amsterdam"),
    }

    cities = list(city_durations.keys())

    def has_direct(a, b):
        return (a, b) in direct_flights or (b, a) in direct_flights

    # Try all city orders and find a feasible one
    for order in itertools.permutations(cities, len(cities)):
        # Must have direct flights between consecutive cities
        if not all(has_direct(order[i], order[i+1]) for i in range(len(order) - 1)):
            continue

        # Build segments with overlaps on transition days:
        # If segment i is [s_i, e_i], then segment i+1 starts at s_{i+1} = e_i (travel day counts for both)
        starts = {}
        ends = {}
        current_start = 1
        feasible = True

        for city in order:
            duration = city_durations[city]
            s = current_start
            e = s + duration - 1
            starts[city] = s
            ends[city] = e

            # Check window constraints (if any)
            if city in city_windows:
                w_start, w_end = city_windows[city]
                if not (s <= w_start and e >= w_end):
                    feasible = False
                    break

            # Next segment starts on this segment's end day (overlap on travel day)
            current_start = e

        if not feasible:
            continue

        # Verify the itinerary spans exactly total_days (by construction this should hold)
        if ends[order[-1]] != total_days:
            # If not, skip this order
            continue

        # Verify day counts including overlaps match requested durations
        day_to_cities = {d: [] for d in range(1, total_days + 1)}
        for city in order:
            for d in range(starts[city], ends[city] + 1):
                day_to_cities[d].append(city)

        # Each day should have 1 or 2 cities (2 on travel days)
        if any(len(day_to_cities[d]) not in (1, 2) for d in day_to_cities):
            continue

        # Count days per city (including overlap)
        counted_days = {city: 0 for city in cities}
        for d in range(1, total_days + 1):
            for city in day_to_cities[d]:
                counted_days[city] += 1

        if any(counted_days[city] != city_durations[city] for city in cities):
            continue

        # If we reach here, we found a valid itinerary
        itinerary = []
        for city in order:
            itinerary.append({
                "day_range": f"Day {starts[city]}-{ends[city]}",
                "place": city
            })
        return {"itinerary": itinerary}

    # If no plan found (shouldn't happen with given constraints), return empty
    return {"itinerary": []}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))