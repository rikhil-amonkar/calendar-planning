import json
import itertools
from collections import defaultdict

def compute_itinerary():
    # Input variables (constraints)
    trip_length = 16
    cities_required_days = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2,
    }
    direct_flight_pairs = [
        ("Valencia", "Frankfurt"),
        ("Manchester", "Frankfurt"),
        ("Naples", "Manchester"),
        ("Naples", "Frankfurt"),
        ("Naples", "Oslo"),
        ("Oslo", "Frankfurt"),
        ("Vilnius", "Frankfurt"),
        ("Oslo", "Vilnius"),
        ("Manchester", "Oslo"),
        ("Valencia", "Naples"),
    ]
    show_in_frankfurt_days = set([13, 14, 15, 16])  # must attend, be in FRA these days
    wedding_vilnius_days = set([12, 13])  # must be in Vilnius these days (across the night 12->13)

    cities = list(cities_required_days.keys())

    # Build undirected adjacency
    adj = defaultdict(set)
    for a, b in direct_flight_pairs:
        adj[a].add(b)
        adj[b].add(a)

    # We require final two cities to be Vilnius -> Frankfurt to satisfy the day-12/13 wedding and day-13..16 show
    last_city = "Frankfurt"
    penultimate_city = "Vilnius"

    # We require the city before Vilnius to be Oslo (only direct to Vilnius that helps sequence)
    fixed_fourth = "Oslo"

    # Remaining cities to permute for the first three positions
    remaining_first_three = sorted(set(cities) - {last_city, penultimate_city, fixed_fourth})

    def valid_path(seq):
        # Check direct flights exist between each consecutive pair
        return all(seq[i+1] in adj[seq[i]] for i in range(len(seq)-1))

    found_sequence = None
    # Try all permutations of the first three cities
    for perm in itertools.permutations(remaining_first_three):
        candidate = list(perm) + [fixed_fourth, penultimate_city, last_city]
        if valid_path(candidate):
            found_sequence = candidate
            break

    if not found_sequence:
        raise RuntimeError("No valid city visitation sequence found respecting direct flights and constraints.")

    # Compute day ranges using overlap-on-flight rule.
    itinerary = []
    start_day = 1
    day_coverage_by_city = defaultdict(set)

    for i, city in enumerate(found_sequence):
        required = cities_required_days[city]
        end_day = start_day + required - 1  # flight day overlaps count for both consecutive cities
        # Record itinerary segment
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # Fill day coverage for constraint verification
        for d in range(start_day, end_day + 1):
            day_coverage_by_city[city].add(d)
        # Next city's start day equals this end_day (overlap on flight day)
        start_day = end_day

    # Validate total trip length ends on day trip_length
    final_end_day_str = itinerary[-1]["day_range"].split("-")[-1]
    final_end_day = int(final_end_day_str)
    if final_end_day != trip_length:
        raise RuntimeError(f"Constructed itinerary ends on day {final_end_day}, expected {trip_length}.")

    # Validate per-city day counts match requirements
    for city, req in cities_required_days.items():
        if len(day_coverage_by_city[city]) != req:
            raise RuntimeError(f"City {city} has {len(day_coverage_by_city[city])} days, required {req}.")

    # Validate show in Frankfurt days
    fra_days = day_coverage_by_city["Frankfurt"]
    if not show_in_frankfurt_days.issubset(fra_days):
        raise RuntimeError("Frankfurt show days are not fully covered by the itinerary.")

    # Validate Vilnius wedding coverage
    vilnius_days = day_coverage_by_city["Vilnius"]
    if not wedding_vilnius_days.issubset(vilnius_days):
        raise RuntimeError("Vilnius wedding days are not fully covered by the itinerary.")

    # Validate direct flights for the concrete transition days
    # Transition days are the start_day of each city after the first.
    # Ensure each transition corresponds to a direct flight.
    for i in range(len(found_sequence) - 1):
        a = found_sequence[i]
        b = found_sequence[i + 1]
        if b not in adj[a]:
            raise RuntimeError(f"No direct flight between {a} and {b} for transition.")

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))