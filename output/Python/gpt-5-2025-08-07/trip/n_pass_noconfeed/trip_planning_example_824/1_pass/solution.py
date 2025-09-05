import json
from itertools import permutations

def add_bidirectional(graph, a, b):
    graph.setdefault(a, set()).add(b)
    graph.setdefault(b, set()).add(a)

def add_directed(graph, a, b):
    graph.setdefault(a, set()).add(b)

def day_range_str(s, e):
    return f"Day {s}-{e}"

def compute_itinerary():
    # Input variables (constraints)
    total_days = 22
    required_stays = {
        "Berlin": 5,
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5,
    }
    # Fixed windows for mandatory presence
    # - Berlin days 1-5 (annual show)
    # - Lyon must overlap days 7-11 (wedding) and total stay 5; we place exactly 7-11
    # - Bucharest days 13-15 (visiting relatives)
    fixed_windows = {
        "Berlin": (1, 5),
        "Lyon": (7, 11),
        "Bucharest": (13, 15),
    }

    # Build direct flights graph
    flights = {}
    add_bidirectional(flights, "Lisbon", "Bucharest")
    add_bidirectional(flights, "Berlin", "Lisbon")
    add_bidirectional(flights, "Bucharest", "Riga")
    add_bidirectional(flights, "Berlin", "Riga")
    add_bidirectional(flights, "Split", "Lyon")
    add_bidirectional(flights, "Lisbon", "Riga")
    add_directed(flights, "Riga", "Tallinn")  # one-way
    add_bidirectional(flights, "Berlin", "Split")
    add_bidirectional(flights, "Lyon", "Lisbon")
    add_bidirectional(flights, "Berlin", "Tallinn")
    add_bidirectional(flights, "Lyon", "Bucharest")

    # Helper to choose a bridge city between two fixed windows
    def choose_bridge_city(prev_city, prev_end, next_city, next_start, disallowed):
        avail_days = (next_start - prev_end) + 1  # inclusive of both flight days
        candidates = []
        for c, d in required_stays.items():
            if c in disallowed:
                continue
            if d != avail_days:
                continue
            if prev_city in flights and c in flights[prev_city] and c in flights and next_city in flights[c]:
                candidates.append(c)
        candidates.sort()
        return candidates[0] if candidates else None

    # We must avoid extending Lyon beyond its 5-day fixed window (7-11).
    # To reach Bucharest on day 13 while not adding extra Lyon days,
    # we must depart Lyon on day 11 to an intermediate city M, then fly to Bucharest on day 13.
    # Choose M such that Lyon->M and M->Bucharest are direct and duration(M) == (13 - 11 + 1) = 3.
    post_lyon_bridge = choose_bridge_city(
        prev_city="Lyon",
        prev_end=fixed_windows["Lyon"][1],
        next_city="Bucharest",
        next_start=fixed_windows["Bucharest"][0],
        disallowed={"Berlin", "Lyon", "Bucharest"}
    )
    if post_lyon_bridge is None:
        raise ValueError("No valid intermediate city between Lyon and Bucharest found that satisfies constraints.")

    # For the gap between Berlin (ends day 5) and Lyon (starts day 7),
    # we also need an intermediate city X with duration == (7 - 5 + 1) = 3 and direct flights Berlin->X and X->Lyon.
    pre_lyon_bridge = choose_bridge_city(
        prev_city="Berlin",
        prev_end=fixed_windows["Berlin"][1],
        next_city="Lyon",
        next_start=fixed_windows["Lyon"][0],
        disallowed={"Berlin", "Lyon", "Bucharest", post_lyon_bridge}
    )
    if pre_lyon_bridge is None:
        raise ValueError("No valid intermediate city between Berlin and Lyon found that satisfies constraints.")

    # Build itinerary blocks with (city, start_day, end_day)
    blocks = []
    # Fixed Berlin
    blocks.append(("Berlin", fixed_windows["Berlin"][0], fixed_windows["Berlin"][1]))
    # Bridge city between Berlin and Lyon
    blocks.append((pre_lyon_bridge, fixed_windows["Berlin"][1], fixed_windows["Lyon"][0]))
    # Fixed Lyon
    blocks.append(("Lyon", fixed_windows["Lyon"][0], fixed_windows["Lyon"][1]))
    # Bridge city between Lyon and Bucharest (post-Lyon)
    blocks.append((post_lyon_bridge, fixed_windows["Lyon"][1], fixed_windows["Bucharest"][0]))
    # Fixed Bucharest
    blocks.append(("Bucharest", fixed_windows["Bucharest"][0], fixed_windows["Bucharest"][1]))

    # Remaining cities to schedule after Bucharest until day 22
    used_cities = {city for city, _, _ in blocks}
    remaining = [c for c in required_stays.keys() if c not in used_cities]

    # We must chain remaining cities starting with a flight on day fixed_windows["Bucharest"][1] (day 15),
    # and end exactly on day total_days. Each city c occupies duration d days inclusive, with flight on its end day to next.
    def plan_tail(start_city, start_day, remaining_cities, end_day):
        for order in permutations(remaining_cities):
            valid = True
            prev = start_city
            current_start = start_day
            planned = []
            for c in order:
                # Check direct flight from prev to c
                if prev not in flights or c not in flights[prev]:
                    valid = False
                    break
                d = required_stays[c]
                c_start = current_start
                c_end = c_start + d - 1
                planned.append((c, c_start, c_end))
                prev = c
                current_start = c_end  # next city flight occurs on this end day
            if not valid:
                continue
            # Check we end precisely on end_day
            if planned and planned[-1][2] == end_day:
                return planned
        return None

    tail_plan = plan_tail("Bucharest", fixed_windows["Bucharest"][1], remaining, total_days)
    if tail_plan is None:
        raise ValueError("Could not plan the remaining cities to end exactly on the total trip day with direct flights.")

    # Combine all blocks
    blocks.extend(tail_plan)

    # Validation: build day-to-cities map
    day_to_cities = {day: set() for day in range(1, total_days + 1)}
    # When transitioning from one block to the next, ensure adjacency and that flight occurs on next_block.start_day
    ordered_blocks = sorted(blocks, key=lambda x: (x[1], x[2], x[0]))

    # Validate flight connectivity in sequence of travel by constructing the travel order
    # The intended travel order is the order in which blocks start (ties broken by domain logic)
    travel_order = []
    # Manually construct the intended travel order based on actual path:
    # Start at Berlin, then pre-lyon bridge, then Lyon, then post-lyon bridge, then Bucharest, then the tail cities in their order.
    # To ensure correct order, we sort by start day (stable for overlaps).
    travel_order = sorted(blocks, key=lambda x: x[1])

    # Populate day_to_cities and validate durations
    for city, s, e in blocks:
        for day in range(s, e + 1):
            if 1 <= day <= total_days:
                day_to_cities[day].add(city)

    # Ensure every day is covered by at least one city
    for day in range(1, total_days + 1):
        if not day_to_cities[day]:
            raise AssertionError(f"Uncovered day found: Day {day}")

    # Validate required durations per city
    actual_stays = {c: 0 for c in required_stays}
    for day in range(1, total_days + 1):
        for c in day_to_cities[day]:
            actual_stays[c] += 1

    for c, req in required_stays.items():
        if actual_stays[c] != req:
            raise AssertionError(f"City {c} has {actual_stays[c]} days but requires {req}.")

    # Validate fixed window presence
    for c, (s, e) in fixed_windows.items():
        for day in range(s, e + 1):
            if c not in day_to_cities[day]:
                raise AssertionError(f"City {c} not present on required day {day}.")

    # Validate all flights between consecutive blocks in travel order are direct
    for i in range(len(travel_order) - 1):
        a_city, a_s, a_e = travel_order[i]
        b_city, b_s, b_e = travel_order[i + 1]
        # Flight occurs on b_s day; ensure adjacency and the overlap day matches (a_e == b_s)
        if b_city not in flights.get(a_city, set()):
            raise AssertionError(f"No direct flight from {a_city} to {b_city}.")
        if a_e != b_s:
            raise AssertionError(f"Flight day mismatch between {a_city} ({a_s}-{a_e}) and {b_city} ({b_s}-{b_e}).")

    # Final structure for output
    # Sort blocks by start day for presentation
    itinerary_blocks = sorted(blocks, key=lambda x: x[1])
    itinerary = [{"day_range": day_range_str(s, e), "place": city} for city, s, e in itinerary_blocks]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))