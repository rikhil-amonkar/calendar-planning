import json

def plan_itinerary():
    # Input variables (constraints)
    total_days = 20
    cities = ["Venice", "Edinburgh", "Krakow", "Stuttgart", "Split", "Athens", "Mykonos"]  # route order
    durations = {
        "Venice": 5,
        "Edinburgh": 4,
        "Krakow": 4,
        "Stuttgart": 3,
        "Split": 2,
        "Athens": 4,
        "Mykonos": 4,
    }
    # Direct flights (undirected edges)
    direct_flights = {
        frozenset({"Krakow", "Split"}),
        frozenset({"Split", "Athens"}),
        frozenset({"Edinburgh", "Krakow"}),
        frozenset({"Venice", "Stuttgart"}),
        frozenset({"Krakow", "Stuttgart"}),
        frozenset({"Edinburgh", "Stuttgart"}),
        frozenset({"Stuttgart", "Athens"}),
        frozenset({"Venice", "Edinburgh"}),
        frozenset({"Athens", "Mykonos"}),
        frozenset({"Venice", "Athens"}),
        frozenset({"Stuttgart", "Split"}),
        frozenset({"Edinburgh", "Athens"}),
    }
    # Must-attend workshop window in Stuttgart (inclusive)
    workshop_city = "Stuttgart"
    workshop_window = (11, 13)  # inclusive
    # Meeting windows
    krakow_meet_city = "Krakow"
    krakow_meet_window = (8, 11)  # inclusive, need at least one day overlap
    split_meet_city = "Split"
    split_meet_window = (13, 14)  # inclusive, need at least one day overlap

    # Route validity check (only direct flights between consecutive cities)
    for i in range(len(cities) - 1):
        pair = frozenset({cities[i], cities[i + 1]})
        if pair not in direct_flights:
            raise ValueError(f"No direct flight between {cities[i]} and {cities[i+1]}")

    # Compute start/end days for each city ensuring:
    # - Workshop city covers its required window
    # - Each city gets the exact duration requested
    # - Overlaps on flight days are allowed (end of city A == start of city B is a flight day counted for both)
    start_days = {}
    end_days = {}

    # Anchor the workshop city
    wk_start, wk_end = workshop_window
    stg_dur = durations[workshop_city]
    required_len = wk_end - wk_start + 1
    if stg_dur < required_len:
        raise ValueError("Stuttgart duration is too short to cover the workshop window.")
    stg_index = cities.index(workshop_city)
    start_days[workshop_city] = wk_start
    end_days[workshop_city] = start_days[workshop_city] + stg_dur - 1
    if end_days[workshop_city] < wk_end:
        raise ValueError("Stuttgart range does not fully include the workshop window.")

    # Backward propagate to earlier cities
    for idx in range(stg_index - 1, -1, -1):
        next_city = cities[idx + 1]
        city = cities[idx]
        # Flight from city -> next_city happens on start_days[next_city]
        end_days[city] = start_days[next_city]
        start_days[city] = end_days[city] - durations[city] + 1

    # Forward propagate to later cities
    for idx in range(stg_index + 1, len(cities)):
        prev_city = cities[idx - 1]
        city = cities[idx]
        # Flight from prev_city -> city happens on end_days[prev_city]
        start_days[city] = end_days[prev_city]
        end_days[city] = start_days[city] + durations[city] - 1

    # Validate calendar bounds
    first_city = cities[0]
    last_city = cities[-1]
    if start_days[first_city] != 1:
        raise ValueError(f"Trip does not start on Day 1 (starts on Day {start_days[first_city]}).")
    if end_days[last_city] != total_days:
        raise ValueError(f"Trip does not end on Day {total_days} (ends on Day {end_days[last_city]}).")

    # Validate durations
    for c in cities:
        actual = end_days[c] - start_days[c] + 1
        if actual != durations[c]:
            raise ValueError(f"Duration mismatch for {c}: expected {durations[c]}, got {actual}.")

    # Validate workshop window coverage
    if not (start_days[workshop_city] <= wk_start and end_days[workshop_city] >= wk_end):
        raise ValueError("Workshop window not fully covered in Stuttgart.")

    # Validate Krakow meeting overlap (at least one day)
    kr_start, kr_end = krakow_meet_window
    k_s, k_e = start_days[krakow_meet_city], end_days[krakow_meet_city]
    if max(kr_start, k_s) > min(kr_end, k_e):
        raise ValueError("No overlap with Krakow meeting window.")

    # Validate Split meeting overlap (at least one day)
    sp_start, sp_end = split_meet_window
    sps, spe = start_days[split_meet_city], end_days[split_meet_city]
    if max(sp_start, sps) > min(sp_end, spe):
        raise ValueError("No overlap with Split friends window.")

    # Validate all days within 1..total_days
    for c in cities:
        if start_days[c] < 1 or end_days[c] > total_days:
            raise ValueError(f"City {c} has days out of bounds.")

    # Optional consistency: sum(city_days) - number_of_flights == total_days
    city_days_total = sum(durations[c] for c in cities)
    number_of_flights = len(cities) - 1
    if city_days_total - number_of_flights != total_days:
        raise ValueError("Day accounting mismatch with overlaps and flights.")

    # Build itinerary output
    itinerary = []
    for c in cities:
        itinerary.append({
            "day_range": f"Day {start_days[c]}-{end_days[c]}",
            "place": c
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_itinerary()
    print(json.dumps(result, ensure_ascii=False))