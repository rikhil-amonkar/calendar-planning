import json
from itertools import permutations

def build_itinerary():
    # Trip constraints (inputs)
    total_days = 16
    cities = ["London", "Split", "Oslo", "Porto"]
    desired_stays = {
        "London": 7,
        "Split": 5,
        "Oslo": 2,
        "Porto": 5,
    }
    # Direct flight adjacency (undirected)
    direct_pairs = [
        ("London", "Oslo"),
        ("Split", "Oslo"),
        ("Oslo", "Porto"),
        ("London", "Split"),
    ]
    direct_flights = {c: set() for c in cities}
    for a, b in direct_pairs:
        direct_flights[a].add(b)
        direct_flights[b].add(a)

    # Special constraints
    london_visit_window = (1, 7)   # Must be in London between days 1 and 7; and total London stay is 7 days
    split_show_window = (7, 11)    # Must be in Split from day 7 through day 11; total Split stay is 5 days

    # Validate special constraints are compatible with desired stays
    assert desired_stays["London"] == (london_visit_window[1] - london_visit_window[0] + 1), \
        "London desired stay must align with the day 1-7 constraint."
    assert desired_stays["Split"] == (split_show_window[1] - split_show_window[0] + 1), \
        "Split desired stay must align with the day 7-11 show."

    # Build the itinerary segments step-by-step:
    segments = []

    # 1) London segment is fixed by the visiting window
    london_start = london_visit_window[0]
    london_end = london_start + desired_stays["London"] - 1
    segments.append(("London", london_start, london_end))

    # 2) Split segment is fixed by the show window
    split_start, split_end = split_show_window
    segments.append(("Split", split_start, split_end))

    # Verify direct flight for London -> Split (travel on day 7 counts for both)
    assert "Split" in direct_flights["London"], "Direct flight required between London and Split."

    # 3) Remaining cities: Oslo and Porto. Sequence must follow direct-flight constraints.
    remaining = [c for c in cities if c not in {"London", "Split"}]

    def try_order(order):
        """Return segments if order is feasible; else None."""
        prev_city = "Split"
        curr_start = split_end  # Next segment starts on the previous segment's end day (travel day counted in both)
        temp_segments = segments.copy()

        # Check flight from Split to first city in order
        first_city = order[0]
        if first_city not in direct_flights[prev_city]:
            return None
        first_start = curr_start
        first_end = first_start + desired_stays[first_city] - 1
        temp_segments.append((first_city, first_start, first_end))

        # Next city
        second_city = order[1]
        # Check flight between first_city and second_city
        if second_city not in direct_flights[first_city]:
            return None
        second_start = first_end
        second_end = second_start + desired_stays[second_city] - 1
        temp_segments.append((second_city, second_start, second_end))

        # Validate total coverage ends on total_days
        if second_end != total_days:
            return None

        # Validate day-by-day presence counts per city equal desired stays
        day_to_cities = {}
        for city, s, e in temp_segments:
            for d in range(s, e + 1):
                day_to_cities.setdefault(d, set()).add(city)

        # Ensure days are fully covered from 1 to total_days
        if set(day_to_cities.keys()) != set(range(1, total_days + 1)):
            return None

        # Validate each city's total presence matches desired stay
        city_day_counts = {c: 0 for c in cities}
        for d in range(1, total_days + 1):
            for c in day_to_cities[d]:
                city_day_counts[c] += 1

        if city_day_counts != desired_stays:
            return None

        # Validate "visit relatives in London between day 1 and day 7" -> we're in London on those days by construction
        # Validate "attend show in Split from day 7 to day 11" -> we're in Split on those days by construction

        # Validate only direct flights used between consecutive segments
        for i in range(len(temp_segments) - 1):
            a_city = temp_segments[i][0]
            b_city = temp_segments[i + 1][0]
            if b_city not in direct_flights[a_city]:
                return None

        return temp_segments

    feasible_segments = None
    for order in permutations(remaining, 2):
        attempt = try_order(order)
        if attempt is not None:
            feasible_segments = attempt
            break

    if feasible_segments is None:
        raise RuntimeError("No feasible itinerary found with given constraints and direct flights.")

    # Build JSON output
    itinerary = []
    for city, s, e in feasible_segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = build_itinerary()
    print(json.dumps(result, ensure_ascii=False))