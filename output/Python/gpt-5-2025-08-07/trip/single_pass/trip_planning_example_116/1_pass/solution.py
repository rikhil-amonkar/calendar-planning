import json

def compute_itinerary(total_days, city_durations, direct_flights, forced_days):
    # Basic validations
    cities = list(city_durations.keys())
    assert len(cities) == 3, "Exactly three cities must be planned."
    for city, dur in city_durations.items():
        assert dur >= 1, f"Duration for {city} must be positive."

    # Flights needed to visit all 3 cities linearly
    required_flights = 2
    assert sum(city_durations.values()) == total_days + required_flights, (
        "Sum of city stays must equal total days + number of flights (because flight days are double-counted)."
    )

    # Determine last city: prefer the one forced on the final day if specified
    if total_days in forced_days:
        last_city = forced_days[total_days]
    else:
        # If not specified, pick any city as last; but here it's specified
        last_city = cities[0]

    # Assign last segment based on its duration so that it ends on total_days
    last_end = total_days
    last_start = last_end - city_durations[last_city] + 1
    if last_start < 1:
        raise ValueError("Last city's duration does not fit into the total timeline.")

    # Validate forced constraints for last city
    for day, city in forced_days.items():
        if city == last_city and not (last_start <= day <= last_end):
            raise ValueError(f"Forced day {day} in {city} cannot be satisfied.")

    remaining_cities = [c for c in cities if c != last_city]

    # Middle city must have a direct flight to the last city and its segment must end on last_start
    middle_candidates = [c for c in remaining_cities if (c, last_city) in direct_flights]

    solutions = []
    for middle_city in middle_candidates:
        mid_end = last_start  # Flight day is counted in both middle and last city
        mid_start = mid_end - city_durations[middle_city] + 1
        if mid_start < 1:
            continue

        # Validate forced constraints for middle city
        ok = True
        for day, city in forced_days.items():
            if city == middle_city and not (mid_start <= day <= mid_end):
                ok = False
                break
        if not ok:
            continue

        # First city is the remaining one; it must connect to middle city
        first_city = [c for c in remaining_cities if c != middle_city][0]
        if (first_city, middle_city) not in direct_flights:
            continue

        first_end = mid_start  # Flight day is counted in both first and middle city
        first_start = first_end - city_durations[first_city] + 1

        # The timeline must start at day 1
        if first_start != 1:
            continue

        # Validate forced constraints for first city
        ok = True
        for day, city in forced_days.items():
            if city == first_city and not (first_start <= day <= first_end):
                ok = False
                break
        if not ok:
            continue

        # Verify contiguous segments covering full range with exactly two overlaps (flight days)
        segments = [
            (first_start, first_end, first_city),
            (mid_start, mid_end, middle_city),
            (last_start, last_end, last_city),
        ]
        segments.sort(key=lambda x: x[0])
        if segments[0][0] != 1 or segments[-1][1] != total_days:
            continue
        contiguous = all(segments[i][1] == segments[i+1][0] for i in range(2))
        if not contiguous:
            continue

        # Verify total flights and city-day accounting
        flights_count = 2
        city_day_total = sum(end - start + 1 for start, end, _ in segments)
        if city_day_total != total_days + flights_count:
            continue

        solutions.append(segments)

    if not solutions:
        raise ValueError("No feasible itinerary found that satisfies all constraints.")

    # Choose the first feasible solution (unique in this setup)
    chosen = solutions[0]
    itinerary = [{"day_range": f"Day {start}-{end}", "place": city} for start, end, city in chosen]
    return itinerary

if __name__ == "__main__":
    # Input variables (constraints)
    total_days = 18
    city_durations = {
        "Split": 6,
        "Santorini": 7,
        "London": 7
    }
    direct_flights = {
        ("London", "Santorini"),
        ("Santorini", "London"),
        ("Split", "London"),
        ("London", "Split")
    }
    forced_days = {
        12: "Santorini",
        18: "Santorini"
    }

    itinerary = compute_itinerary(total_days, city_durations, direct_flights, forced_days)
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))