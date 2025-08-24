import json
import itertools

def compute_itinerary():
    # Input variables
    total_days = 19
    city_day_requirements = {
        "Dubrovnik": 5,
        "Warsaw": 2,
        "Stuttgart": 7,
        "Bucharest": 6,
        "Copenhagen": 3,
    }
    cities = list(city_day_requirements.keys())
    # Undirected direct-flight edges
    direct_flights = {
        frozenset(["Warsaw", "Copenhagen"]),
        frozenset(["Stuttgart", "Copenhagen"]),
        frozenset(["Warsaw", "Stuttgart"]),
        frozenset(["Bucharest", "Copenhagen"]),
        frozenset(["Bucharest", "Warsaw"]),
        frozenset(["Copenhagen", "Dubrovnik"]),
    }
    # Must be in Stuttgart on day 7 and day 13
    must_be_on_days = {
        "Stuttgart": [7, 13]
    }
    # Wedding: must be in Bucharest on at least one day between day 1 and day 6 inclusive
    wedding_city = "Bucharest"
    wedding_window = (1, 6)

    # Helper: check if a given city order is connected via direct flights
    def edges_valid(order):
        for i in range(len(order) - 1):
            if frozenset([order[i], order[i + 1]]) not in direct_flights:
                return False
        return True

    # Build segments for an order using the rule:
    # - City i occupies a continuous segment [s_i, e_i]
    # - s_0 = 1; e_i = s_i + required_days(city_i) - 1
    # - s_{i+1} = e_i (travel day overlaps both cities)
    # This guarantees total sum of required days is met with overlaps counted as flights.
    def build_segments(order):
        segments = {}
        s = 1
        for city in order:
            e = s + city_day_requirements[city] - 1
            segments[city] = (s, e)
            s = e  # Next city starts on the same day (travel day overlap)
        return segments

    # Validate constraints: total days, fixed-day presence, wedding window
    def constraints_ok(segments, order):
        # Actual total days ends at last city's end day
        last_city = order[-1]
        actual_total_days = segments[last_city][1]

        # Check total days
        if actual_total_days != total_days:
            return False

        # Check must-be-on-days constraints
        for city, days in must_be_on_days.items():
            s, e = segments[city]
            for d in days:
                if not (s <= d <= e):
                    return False

        # Check at least one day in wedding window for wedding city
        s_w, e_w = segments[wedding_city]
        start, end = wedding_window
        if e_w < start or s_w > end:
            return False

        return True

    # Build a day-by-day map of places, and mark travel days
    def build_daywise(segments, order):
        day_to_places = {d: [] for d in range(1, total_days + 1)}
        # Fill presence
        for city, (s, e) in segments.items():
            for d in range(s, e + 1):
                if 1 <= d <= total_days:
                    day_to_places[d].append(city)

        # Determine travel days (the boundary days e_i)
        travel_days = {}
        for i in range(len(order) - 1):
            city_from = order[i]
            city_to = order[i + 1]
            d = segments[city_from][1]  # boundary (last day of city_from)
            travel_days[d] = (city_from, city_to)

        # Convert to place strings
        day_to_place_str = {}
        for d in range(1, total_days + 1):
            if d in travel_days:
                a, b = travel_days[d]
                day_to_place_str[d] = f"{a} -> {b} (travel day)"
            else:
                # should be exactly one city on non-travel days
                places = day_to_places[d]
                # Safety: if multiple (shouldn't happen except by travel), join with ' & '
                if len(places) == 1:
                    day_to_place_str[d] = places[0]
                else:
                    day_to_place_str[d] = " & ".join(sorted(places))

        return day_to_place_str

    # Group consecutive days with same place string into ranges
    def group_into_ranges(day_to_place_str):
        itinerary = []
        start = 1
        current = day_to_place_str[1]
        for d in range(2, total_days + 1):
            if day_to_place_str[d] != current:
                # close previous segment
                if start == d - 1:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{d-1}"
                itinerary.append({"day_range": day_range, "place": current})
                start = d
                current = day_to_place_str[d]
        # close last segment
        if start == total_days:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{total_days}"
        itinerary.append({"day_range": day_range, "place": current})
        return itinerary

    # Main search over permutations of city order
    feasible_order = None
    feasible_segments = None
    for order in itertools.permutations(cities):
        if not edges_valid(order):
            continue
        segments = build_segments(order)
        if constraints_ok(segments, order):
            feasible_order = order
            feasible_segments = segments
            break

    # Build output
    if feasible_order is None:
        result = {"itinerary": []}
    else:
        day_to_place_str = build_daywise(feasible_segments, feasible_order)
        itinerary = group_into_ranges(day_to_place_str)
        result = {"itinerary": itinerary}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    compute_itinerary()