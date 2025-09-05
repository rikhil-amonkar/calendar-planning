import json
import itertools

def plan_trip():
    # Input variables (trip constraints)
    total_days = 15
    cities = {
        "Paris": {"required_days": 6},
        "Madrid": {"required_days": 7, "required_window": (1, 7)},      # Attend show Day 1-7
        "Bucharest": {"required_days": 2, "required_window": (14, 15)}, # Visit relatives Day 14-15
        "Seville": {"required_days": 3},
    }
    direct_flights = [
        ("Paris", "Bucharest"),
        ("Seville", "Paris"),
        ("Madrid", "Bucharest"),
        ("Madrid", "Paris"),
        ("Madrid", "Seville"),
    ]

    # Build undirected graph for direct flights
    graph = {c: set() for c in cities.keys()}
    for a, b in direct_flights:
        graph[a].add(b)
        graph[b].add(a)

    # Identify anchored cities (with fixed required windows)
    anchors = {c: info["required_window"] for c, info in cities.items() if "required_window" in info}
    if not anchors:
        raise ValueError("No anchored cities specified; cannot enforce day-based requirements.")

    # Choose start and end anchors algorithmically
    # Start anchor: city whose required window starts at day 1
    start_anchor_candidates = [c for c, w in anchors.items() if w[0] == 1]
    if not start_anchor_candidates:
        raise ValueError("No start anchor begins at Day 1.")
    start_anchor = start_anchor_candidates[0]

    # End anchor: city whose required window ends at total_days
    end_anchor_candidates = [c for c, w in anchors.items() if w[1] == total_days]
    if not end_anchor_candidates:
        raise ValueError("No end anchor ends on the last day.")
    end_anchor = end_anchor_candidates[0]

    # Intermediate cities are those without fixed windows and not anchors
    intermediates = [c for c in cities.keys() if c not in {start_anchor, end_anchor}]

    def has_direct(a, b):
        return b in graph[a]

    # Try all permutations of intermediates to find a feasible ordered route
    solution = None
    for mid_order in itertools.permutations(intermediates):
        ordered_route = [start_anchor] + list(mid_order) + [end_anchor]

        # Check direct flight connectivity along the route
        flights_ok = all(has_direct(ordered_route[i], ordered_route[i+1]) for i in range(len(ordered_route)-1))
        if not flights_ok:
            continue

        # Compute schedule using overlap rule:
        # - Next city starts on the same day the previous city ends (travel day counts for both)
        schedule = {}
        # Fix start anchor exactly to its window
        s_start, s_end = anchors[start_anchor]
        # Validate its duration matches required days
        if s_end - s_start + 1 != cities[start_anchor]["required_days"]:
            continue
        schedule[start_anchor] = (s_start, s_end)

        feasible = True
        prev_city = start_anchor
        for city in ordered_route[1:-1]:
            start = schedule[prev_city][1]
            end = start + cities[city]["required_days"] - 1
            schedule[city] = (start, end)
            prev_city = city

        # Compute for end anchor and validate matches its required window exactly
        start = schedule[prev_city][1]
        end = start + cities[end_anchor]["required_days"] - 1
        if (start, end) != anchors[end_anchor]:
            feasible = False

        if feasible:
            schedule[end_anchor] = (start, end)

            # Final validations
            # - Start at Day 1; End at total_days
            # - Ensure continuity: each next start equals prev end
            if schedule[start_anchor][0] != 1 or schedule[end_anchor][1] != total_days:
                feasible = False
            else:
                # Continuity check
                for i in range(len(ordered_route)-1):
                    c1, c2 = ordered_route[i], ordered_route[i+1]
                    if schedule[c2][0] != schedule[c1][1]:
                        feasible = False
                        break

        if feasible:
            solution = (ordered_route, schedule)
            break

    if solution is None:
        # Fallback minimal JSON in case no solution is found (should not happen with given constraints)
        return {"itinerary": []}

    ordered_route, schedule = solution

    # Build itinerary output
    itinerary = []
    for city in ordered_route:
        start, end = schedule[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))