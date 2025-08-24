import json

def main():
    # Input parameters
    total_days = 16
    cities = ["Dubrovnik", "Munich", "Krakow", "Split", "Milan", "Porto"]
    durations = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5
    }
    # Windows and required attendances
    munich_show_window = (4, 8)   # Must be in Munich from day 4 to 8 inclusive
    krakow_friends_window = (8, 9)  # Must be in Krakow days 8 and 9
    milan_wedding_window = (11, 13) # Must be in Milan between days 11 and 13 inclusive

    # Direct flight graph (undirected)
    edges = {
        frozenset(("Munich", "Porto")),
        frozenset(("Split", "Milan")),
        frozenset(("Milan", "Porto")),
        frozenset(("Munich", "Krakow")),
        frozenset(("Munich", "Milan")),
        frozenset(("Dubrovnik", "Munich")),
        frozenset(("Krakow", "Split")),
        frozenset(("Krakow", "Milan")),
        frozenset(("Munich", "Split")),
    }

    # Helper to build contiguous day ranges
    def contiguous_range(days):
        s, e = min(days), max(days)
        assert set(days) == set(range(s, e + 1)), "Days must be contiguous"
        return (s, e)

    # Step 1: Anchor the fixed windows based on constraints
    munich_days = list(range(munich_show_window[0], munich_show_window[1] + 1))
    assert len(munich_days) == durations["Munich"] == 5

    krakow_days = list(range(krakow_friends_window[0], krakow_friends_window[1] + 1))
    assert len(krakow_days) == durations["Krakow"] == 2

    milan_days = list(range(milan_wedding_window[0], milan_wedding_window[1] + 1))
    assert len(milan_days) == durations["Milan"] == 3

    # Step 2: Deduce Dubrovnik: must end on Munich start day to use direct flight and fit 4 days
    dubrovnik_end = munich_days[0]  # day 4
    dubrovnik_start = dubrovnik_end - durations["Dubrovnik"] + 1
    assert dubrovnik_start >= 1
    dubrovnik_days = list(range(dubrovnik_start, dubrovnik_end + 1))

    # Step 3: Deduce Split: bridge between Krakow (ends at 9) and Milan (starts at 11) with 3 days
    split_start = krakow_days[-1]  # day 9
    split_end = milan_days[0]      # day 11
    split_days = list(range(split_start, split_end + 1))
    assert len(split_days) == durations["Split"] == 3

    # Step 4: Deduce Porto: start on Milan end (13) and occupy 4 days to end of trip
    porto_start = milan_days[-1]
    porto_days = list(range(porto_start, porto_start + durations["Porto"]))
    assert porto_days[-1] == total_days

    # Collect schedules
    city_days = {
        "Dubrovnik": dubrovnik_days,
        "Munich": munich_days,
        "Krakow": krakow_days,
        "Split": split_days,
        "Milan": milan_days,
        "Porto": porto_days
    }

    # Validation: durations
    for c, days in city_days.items:
        assert len(days) == durations[c]

    # Validation: total city-days equals D + number_of_flights
    sum_city_days = sum(len(v) for v in city_days.values())
    required_flights = sum_city_days - total_days
    assert required_flights == len(cities) - 1  # visiting each city once

    # Build route by chronological order (by start day)
    spans = {c: contiguous_range(days) for c, days in city_days.items()}
    ordered = sorted(spans.items(), key=lambda kv: kv[1][0])  # (city, (start, end))

    # Validate edges and overlaps correspond to flights
    # Overlaps should be exactly 1 day between consecutive cities and those cities must be directly connected
    for i in range(len(ordered) - 1):
        city_a, (a_start, a_end) = ordered[i]
        city_b, (b_start, b_end) = ordered[i + 1]
        # Overlap day must be exactly a_end == b_start
        assert a_end == b_start, f"Non-matching overlap between {city_a} and {city_b}"
        assert frozenset((city_a, city_b)) in edges, f"No direct flight between {city_a} and {city_b}"

    # Validate full coverage of 1..16 (union of days equals all trip days)
    covered = set()
    for days in city_days.values():
        covered.update(days)
    assert covered == set(range(1, total_days + 1)), "Coverage of days 1..16 is not complete"

    # Output itinerary
    itinerary = []
    for city, (start, end) in ordered:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()