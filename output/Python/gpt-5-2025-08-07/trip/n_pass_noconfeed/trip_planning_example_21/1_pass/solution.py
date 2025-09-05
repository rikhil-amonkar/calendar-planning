import json

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 10
    cities = ["Mykonos", "Vienna", "Venice"]
    required_days = {
        "Mykonos": 2,
        "Vienna": 4,
        "Venice": 6
    }
    # Direct flights (bidirectional)
    direct_flights = {
        ("Mykonos", "Vienna"), ("Vienna", "Mykonos"),
        ("Vienna", "Venice"), ("Venice", "Vienna")
    }
    # Workshop constraint in Venice: must be there within this inclusive window
    workshop_city = "Venice"
    workshop_start = 5
    workshop_end = 10

    # Helper to check if direct flight exists
    def has_direct(a, b):
        return (a, b) in direct_flights or (b, a) in direct_flights

    # Derive Venice block to fully cover workshop window
    venice_req = required_days[workshop_city]
    window_len = workshop_end - workshop_start + 1

    # Venice block must fully cover the workshop window
    earliest_start = max(1, workshop_end - venice_req + 1)
    latest_start = min(workshop_start, total_days - venice_req + 1)
    possible_starts = [s for s in range(earliest_start, latest_start + 1)]
    if not possible_starts:
        raise ValueError("No feasible Venice block to cover the workshop window with given duration.")
    # Choose earliest feasible start for Venice
    venice_start = possible_starts[0]
    venice_end = venice_start + venice_req - 1
    if not (venice_start <= workshop_start and venice_end >= workshop_end):
        raise ValueError("Venice block does not cover the workshop window.")

    # Determine city order to minimize flights and obey direct routes:
    # Venice must be last block (ends on total_days or workshop_end); predecessor must connect directly to Venice.
    predecessors = [c for c in cities if c != "Venice" and has_direct(c, "Venice")]
    if not predecessors:
        raise ValueError("No city connects directly to Venice for the final leg.")
    # Prefer Vienna as it is required and directly connected
    if "Vienna" not in predecessors:
        raise ValueError("Vienna must precede Venice but is not connected.")
    pre_venice = "Vienna"

    # Remaining city(ies) must connect to Vienna (only Mykonos remains)
    remaining = [c for c in cities if c not in {pre_venice, "Venice"}]
    # Build minimal-flight order
    order = []
    # Start from the remaining city that connects to Vienna
    if len(remaining) != 1 or not has_direct(remaining[0], pre_venice):
        raise ValueError("Unable to form a minimal-flight path covering all cities.")
    order = [remaining[0], pre_venice, "Venice"]  # e.g., ["Mykonos", "Vienna", "Venice"]

    # Validate total days feasibility via overlaps (each flight day counts for both cities)
    flights_count = len(order) - 1
    if sum(required_days[c] for c in order) - flights_count != total_days:
        raise ValueError("Inconsistent total days with required city durations and flight overlaps.")

    # Solve flight days to satisfy durations with two flights:
    # Let flight2 (to Venice) be on venice_start to start Venice block right away.
    flight2_day = venice_start  # Vienna -> Venice on this day

    # Vienna spans from flight1_day to flight2_day inclusive; its count must equal required_days["Vienna"]
    # So flight1_day = flight2_day - Vienna_required + 1
    vienna_req = required_days["Vienna"]
    flight1_day = flight2_day - vienna_req + 1  # Mykonos -> Vienna on this day

    # Starting city block (order[0]) begins on day 1; its duration equals flight1_day
    start_city = order[0]
    if flight1_day < 1 or flight1_day >= flight2_day:
        raise ValueError("Invalid computed flight days.")
    if required_days[start_city] != flight1_day:
        raise ValueError("Cannot match starting city required days with two-flight plan.")

    # Build day-to-cities presence map considering flights count for both cities on flight days
    day_to_cities = {d: set() for d in range(1, total_days + 1)}

    # From Day 1 to flight1_day: in start_city (Mykonos), include flight day
    for d in range(1, flight1_day + 1):
        day_to_cities[d].add(start_city)
    # On flight1_day, also in Vienna
    day_to_cities[flight1_day].add("Vienna")
    # From flight1_day+1 to flight2_day-1: in Vienna
    for d in range(flight1_day + 1, flight2_day):
        day_to_cities[d].add("Vienna")
    # On flight2_day, in Vienna and Venice
    day_to_cities[flight2_day].update({"Vienna", "Venice"})
    # From flight2_day+1 to total_days: in Venice
    for d in range(flight2_day + 1, total_days + 1):
        day_to_cities[d].add("Venice")

    # Validate per-city day counts
    counts = {c: sum(1 for d in day_to_cities if c in day_to_cities[d]) for c in cities}
    for c in cities:
        if counts[c] != required_days[c]:
            raise ValueError(f"City {c} has {counts[c]} days, expected {required_days[c]}.")

    # Validate workshop coverage
    for d in range(workshop_start, workshop_end + 1):
        if workshop_city not in day_to_cities[d]:
            raise ValueError("Workshop days are not fully covered in Venice.")

    # Validate that we only move along direct flights on flight days:
    # Detect transitions between consecutive days and ensure they are via allowed flights and counted on the transition day
    # Extract flight days by detecting day where a city appears then disappears next day and another city appears
    # For our deterministic plan, check the two known flights
    if not has_direct(start_city, "Vienna"):
        raise ValueError(f"No direct flight between {start_city} and Vienna.")
    if not has_direct("Vienna", "Venice"):
        raise ValueError("No direct flight between Vienna and Venice.")

    # Build itinerary as a list of contiguous ranges per city in visit order
    def collapse_city_ranges(city):
        days = sorted([d for d in range(1, total_days + 1) if city in day_to_cities[d]])
        if not days:
            return []
        ranges = []
        start = prev = days[0]
        for d in days[1:]:
            if d == prev + 1:
                prev = d
            else:
                ranges.append((start, prev))
                start = prev = d
        ranges.append((start, prev))
        return ranges

    itinerary = []
    for city in order:
        for (a, b) in collapse_city_ranges(city):
            itinerary.append({
                "day_range": f"Day {a}-{b}",
                "place": city
            })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))