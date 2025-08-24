import json
from itertools import permutations

def compute_itinerary():
    # Input variables (constraints)
    total_days = 9
    cities = ["Vienna", "Nice", "Stockholm", "Split"]
    required_days = {
        "Vienna": 2,
        "Nice": 2,
        "Stockholm": 5,
        "Split": 3,
    }
    # Direct flights (undirected)
    direct_pairs = {
        ("Vienna", "Stockholm"),
        ("Vienna", "Nice"),
        ("Vienna", "Split"),
        ("Stockholm", "Split"),
        ("Nice", "Stockholm"),
    }
    adjacency = {}
    for a, b in direct_pairs:
        adjacency.setdefault(a, set()).add(b)
        adjacency.setdefault(b, set()).add(a)

    # Special day constraints
    must_be_on = {
        7: "Split",
        9: "Split",
    }
    workshop_city = "Vienna"
    workshop_days = [1, 2]  # must be in Vienna on these days

    # Helper to verify direct flight existence
    def has_direct(a, b):
        return b in adjacency.get(a, set())

    # Determine start and end cities from constraints
    start_city = workshop_city
    end_city = must_be_on[9]  # must be in Split on day 9; thus end there
    remaining = [c for c in cities if c not in (start_city, end_city)]

    # Compute the arrival day to end_city to satisfy its required days and day 9 constraint
    # To have exactly required_days[end_city] ending on total_days:
    # end city occupancy must be days [end_start_day .. total_days]
    end_required = required_days[end_city]
    end_start_day = total_days - (end_required - 1)

    # Validate must_be_on days are within end city occupancy
    for day, city in must_be_on.items():
        if city == end_city:
            if not (end_start_day <= day <= total_days):
                raise ValueError("End city 'must_be_on' day is incompatible with required days.")

    # Try permutations for middle cities to satisfy direct flight connectivity
    found = None
    for mid1, mid2 in permutations(remaining, 2):
        # Check direct flight path start->mid1->mid2->end
        if not (has_direct(start_city, mid1) and has_direct(mid1, mid2) and has_direct(mid2, end_city)):
            continue

        # Determine flight days by working backward from end_start_day and required days
        mid2_required = required_days[mid2]
        # mid2 spans from mid2_start to end_start_day inclusive
        mid2_start_day = end_start_day - (mid2_required - 1)

        mid1_required = required_days[mid1]
        # mid1 spans from mid1_start to mid2_start_day inclusive
        mid1_start_day = mid2_start_day - (mid1_required - 1)

        # start_city spans from day 1 to mid1_start_day inclusive
        start_span_days = mid1_start_day  # since it's Day 1..mid1_start_day inclusive
        if start_span_days != required_days[start_city]:
            # Not matching required days for the start city; try next permutation
            continue

        # Derived flight days (one flight per segment, on the inclusive boundary days)
        flight_day_1 = mid1_start_day         # start_city -> mid1
        flight_day_2 = mid2_start_day         # mid1 -> mid2
        flight_day_3 = end_start_day          # mid2 -> end_city

        # Validate day ranges are within [1..total_days] and strictly increasing
        if not (1 <= flight_day_1 <= total_days and
                1 <= flight_day_2 <= total_days and
                1 <= flight_day_3 <= total_days and
                flight_day_1 < flight_day_2 < flight_day_3):
            continue

        # Build day-to-cities presence map based on contiguous spans (flights at shared boundaries)
        day_to_cities = {d: set() for d in range(1, total_days + 1)}

        # City spans:
        spans = {
            start_city: (1, flight_day_1),
            mid1: (flight_day_1, flight_day_2),
            mid2: (flight_day_2, flight_day_3),
            end_city: (flight_day_3, total_days),
        }

        for city, (s, e) in spans.items():
            for d in range(s, e + 1):
                day_to_cities[d].add(city)

        # Verify required day counts per city
        counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            for c in day_to_cities[d]:
                counts[c] += 1

        if counts != required_days:
            continue

        # Ensure special day constraints are met
        ok = True
        for d in workshop_days:
            if start_city not in day_to_cities[d]:
                ok = False
                break
        for d, city in must_be_on.items():
            if city not in day_to_cities[d]:
                ok = False
                break
        if not ok:
            continue

        # Verify exactly 3 flight days (days with 2 cities), and each is a direct flight day between the correct adjacent cities
        flight_days = [d for d in range(1, total_days + 1) if len(day_to_cities[d]) == 2]
        if len(flight_days) != 3:
            continue

        # Check the specific direct flights on those days match the path order
        # Expected flight days and pairs:
        expected_flights = {
            flight_day_1: (start_city, mid1),
            flight_day_2: (mid1, mid2),
            flight_day_3: (mid2, end_city),
        }
        for d in flight_days:
            pair = tuple(sorted(day_to_cities[d]))
            expected_pair = tuple(sorted(expected_flights[d]))
            if pair != expected_pair or not has_direct(*expected_flights[d]):
                ok = False
                break
        if not ok:
            continue

        found = {
            "order": [start_city, mid1, mid2, end_city],
            "spans": spans,
        }
        break

    if not found:
        raise RuntimeError("No valid itinerary satisfying all constraints was found.")

    # Convert spans to the required itinerary output format
    itinerary = []
    for city in found["order"]:
        s, e = found["spans"][city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))