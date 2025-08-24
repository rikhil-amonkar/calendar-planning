import json

def build_edges(edge_descriptions):
    edges = set()
    for desc in edge_descriptions:
        desc = desc.strip()
        if desc.lower().startswith("from "):
            # format: from A to B
            _, rest = desc.split("from ", 1)
            a, b = rest.split(" to ")
            edges.add((a.strip(), b.strip()))
        elif " and " in desc:
            a, b = desc.split(" and ")
            a = a.strip()
            b = b.strip()
            edges.add((a, b))
            edges.add((b, a))
        else:
            raise ValueError(f"Unrecognized edge format: {desc}")
    return edges

def compute_itinerary():
    total_days = 28

    # Desired durations per city
    durations = {
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5,
        "London": 3,
    }

    # Fixed-day windows constraints (inclusive, absolute trip days)
    fixed_windows = {
        "London": (1, 3),        # Annual show Day 1-3
        "Milan": (3, 7),         # Meet friends Day 3-7
        "Zurich": (7, 8),        # Conference Day 7-8
        "Reykjavik": (9, 13),    # Visit relatives Day 9-13
    }

    # Direct flights list as provided
    edge_descriptions = [
        "London and Hamburg", "London and Reykjavik", "Milan and Barcelona",
        "Reykjavik and Barcelona", "from Reykjavik to Stuttgart", "Stockholm and Reykjavik",
        "London and Stuttgart", "Milan and Zurich", "London and Barcelona",
        "Stockholm and Hamburg", "Zurich and Barcelona", "Stockholm and Stuttgart",
        "Milan and Hamburg", "Stockholm and Tallinn", "Hamburg and Bucharest",
        "London and Bucharest", "Milan and Stockholm", "Stuttgart and Hamburg",
        "London and Zurich", "Milan and Reykjavik", "London and Stockholm",
        "Milan and Stuttgart", "Stockholm and Barcelona", "London and Milan",
        "Zurich and Hamburg", "Bucharest and Barcelona", "Zurich and Stockholm",
        "Barcelona and Tallinn", "Zurich and Tallinn", "Hamburg and Barcelona",
        "Stuttgart and Barcelona", "Zurich and Reykjavik", "Zurich and Bucharest"
    ]
    edges = build_edges(edge_descriptions)

    # Validate high-level feasibility: sum of city-days = total_days + number_of_flights.
    S = sum(durations.values())
    # With N cities visited once, there are N-1 flights (each on a single day, overlapping counts by +1)
    N = len(durations)
    if S - (N - 1) != total_days:
        raise ValueError("Durations do not align with trip length and flight overlap requirement.")

    # Pre-seed sequence with fixed-window core cities in chronological order
    sequence = ["London", "Milan", "Zurich"]

    # Insert a 2-day bridging city between Zurich (ends Day 8) and Reykjavik (starts Day 9)
    # Requirements: duration 2; direct flights Zurich->City and City->Reykjavik
    remaining_cities = set(durations.keys()) - set(sequence)
    bridge_candidates = [
        c for c in remaining_cities
        if durations[c] == 2 and ("Zurich", c) in edges and (c, "Reykjavik") in edges and c not in fixed_windows
    ]
    if not bridge_candidates:
        raise ValueError("No suitable 2-day bridging city found between Zurich and Reykjavik.")
    bridge_city = bridge_candidates[0]  # deterministic pick
    sequence.append(bridge_city)
    sequence.append("Reykjavik")

    remaining_cities -= {bridge_city, "Reykjavik"}

    # From Reykjavik on Day 13, prefer using the one-way "from Reykjavik to Stuttgart"
    current = "Reykjavik"
    if ("Reykjavik", "Stuttgart") in edges and "Stuttgart" in remaining_cities:
        sequence.append("Stuttgart")
        remaining_cities.remove("Stuttgart")
        current = "Stuttgart"
    else:
        # Fallback: pick any remaining city reachable directly
        candidates = [c for c in remaining_cities if (current, c) in edges]
        if not candidates:
            raise ValueError("No city reachable directly from Reykjavik to continue the itinerary.")
        pick = candidates[0]
        sequence.append(pick)
        remaining_cities.remove(pick)
        current = pick

    # Greedy chain through remaining cities ensuring direct connections and a feasible end on Day 28
    # We target a specific, strongly connected chain to satisfy constraints and edges:
    preferred_chain = ["Hamburg", "Bucharest", "Barcelona", "Tallinn"]
    # Append other remaining (if any) after the preferred chain
    preferred_chain += [c for c in remaining_cities if c not in preferred_chain]

    for city in preferred_chain:
        if city not in remaining_cities:
            continue
        if (current, city) not in edges:
            raise ValueError(f"No direct flight from {current} to {city} to continue the itinerary.")
        sequence.append(city)
        remaining_cities.remove(city)
        current = city

    if remaining_cities:
        raise ValueError(f"Unscheduled cities remain: {remaining_cities}")

    # Now compute day intervals per city following constraints and durations
    intervals = {}
    # Seed known fixed windows first
    for city, (fs, fe) in fixed_windows.items():
        if fe - fs + 1 != durations[city]:
            # All fixed windows in this scenario match durations exactly by design
            raise ValueError(f"Fixed window for {city} does not match duration.")
        intervals[city] = (fs, fe)

    # Build sequentially following the predetermined sequence, aligning to fixed windows where present
    # The rule: next city starts on the previous city's end day (flight day overlap).
    # We trust the fixed windows are consistent: London:1-3 -> Milan:3-7 -> Zurich:7-8 -> bridge:8-9 -> Reykjavik:9-13
    # Then continue sequentially.
    # Ensure Day 1 start
    if sequence[0] != "London":
        raise ValueError("Sequence must start in London to honor the Day 1-3 show.")
    # Validate initial segments (London, Milan, Zurich, bridge, Reykjavik) fixed dates
    expected_initial = [
        ("London", (1, 3)),
        ("Milan", (3, 7)),
        ("Zurich", (7, 8)),
        (bridge_city, (8, 9)),
        ("Reykjavik", (9, 13)),
    ]
    # Assign the bridge city fixed interval (8-9) derived from Zurich(7-8) and Reykjavik(9-13)
    intervals[bridge_city] = (8, 9)

    for city, (s, e) in expected_initial:
        if city not in intervals:
            # Assign if not yet set (bridge was set above; others were in fixed_windows)
            intervals[city] = (s, e)
        else:
            if intervals[city] != (s, e):
                raise ValueError(f"Pre-fixed window mismatch for {city}: {intervals[city]} vs expected {(s, e)}")

    # Continue after Reykjavik
    # Find index of Reykjavik in sequence
    idx_rvk = sequence.index("Reykjavik")
    # The end of Reykjavik
    prev_end = intervals["Reykjavik"][1]

    for i in range(idx_rvk + 1, len(sequence)):
        city = sequence[i]
        dur = durations[city]
        start = prev_end  # flight day overlap
        end = start + dur - 1
        # Ensure not to violate total days
        if end > total_days:
            raise ValueError(f"Scheduling {city} would exceed total trip days.")
        # Ensure edges between previous and current
        prev_city = sequence[i - 1]
        if (prev_city, city) not in edges:
            raise ValueError(f"No direct flight from {prev_city} to {city}.")
        intervals[city] = (start, end)
        prev_end = end

    # Final validation: last day must be total_days
    last_city = sequence[-1]
    if intervals[last_city][1] != total_days:
        raise ValueError(f"Trip does not end on Day {total_days}. Ends on Day {intervals[last_city][1]} instead.")

    # Verify durations match
    for city, (s, e) in intervals.items():
        calc = e - s + 1
        if calc != durations[city]:
            raise ValueError(f"Duration mismatch for {city}: got {calc}, expected {durations[city]}")

    # Verify all edges between consecutive cities
    for a, b in zip(sequence, sequence[1:]):
        if (a, b) not in edges:
            raise ValueError(f"Invalid transition (no direct flight): {a} -> {b}")

    # Verify that on Day 7-8 we are in Zurich and on Day 3-7 in Milan, Day 1-3 in London, Day 9-13 in Reykjavik
    assert intervals["London"] == (1, 3)
    assert intervals["Milan"] == (3, 7)
    assert intervals["Zurich"] == (7, 8)
    assert intervals["Reykjavik"] == (9, 13)

    # Build itinerary output
    itinerary = []
    for city in sequence:
        s, e = intervals[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))