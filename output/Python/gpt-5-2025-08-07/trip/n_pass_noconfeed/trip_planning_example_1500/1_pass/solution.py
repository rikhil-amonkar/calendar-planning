import json
from typing import Dict, List, Tuple, Set, Optional

def parse_flights(flight_descriptions: List[str]) -> Dict[str, Set[str]]:
    adj = {}
    def add_city(c):
        if c not in adj:
            adj[c] = set()
    for desc in flight_descriptions:
        desc = desc.strip()
        if " and " in desc:
            a, b = [x.strip() for x in desc.split(" and ")]
            add_city(a); add_city(b)
            adj[a].add(b)
            adj[b].add(a)
        elif desc.startswith("from ") and " to " in desc:
            parts = desc.split()
            # Expect format: from X to Y
            # Safely parse by removing "from " prefix and splitting by " to "
            rest = desc[len("from "):]
            a, b = [x.strip() for x in rest.split(" to ")]
            add_city(a); add_city(b)
            adj[a].add(b)
        else:
            # Fallback: ignore malformed entries
            pass
    return adj

def find_bridge_city_2days(adj: Dict[str, Set[str]],
                           two_day_cities: Set[str],
                           from_city: str,
                           to_city: str,
                           exclude: Set[str]) -> Optional[str]:
    # Find a 2-day city (not in exclude) such that from_city -> bridge and bridge -> to_city exist
    for c in sorted(two_day_cities - exclude):
        if (from_city in adj) and (c in adj[from_city]) and (c in adj) and (to_city in adj[c]):
            return c
    return None

def dfs_path(start: str, remaining: Set[str], adj: Dict[str, Set[str]]) -> Optional[List[str]]:
    # Find an ordering visiting all nodes in 'remaining' exactly once starting from 'start'
    path = [start]
    used = {start}
    rem_list = list(remaining)

    def backtrack(curr):
        if len(path) == len(remaining):
            return True
        for nxt in sorted(remaining - used):
            if curr in adj and nxt in adj[curr]:
                used.add(nxt)
                path.append(nxt)
                if backtrack(nxt):
                    return True
                path.pop()
                used.remove(nxt)
        return False

    if backtrack(start):
        return path
    return None

def find_sequence_from_source(source: str, remaining: Set[str], adj: Dict[str, Set[str]]) -> Optional[List[str]]:
    # Try all candidates that are directly reachable from 'source' as the first node in the sequence
    candidates = sorted([c for c in remaining if source in adj and c in adj[source]])
    for start in candidates:
        path = dfs_path(start, remaining, adj)
        if path:
            # Validate that source -> start is an edge
            if start in adj.get(source, set()):
                return path
    return None

def compute_itinerary():
    # Input variables
    cities = [
        "London", "Zurich", "Bucharest", "Hamburg", "Barcelona",
        "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"
    ]
    durations = {
        "London": 3,
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5
    }
    total_days = 28

    # Event/fixed-window constraints
    london_show_days = (1, 3)        # Must be in London days 1-3
    zurich_conference_days = (7, 8)  # Must be in Zurich days 7-8
    reykjavik_relatives_days = (9, 13)  # Must be in Reykjavik days 9-13
    milan_friends_window = (3, 7)    # Must be in Milan between days 3-7, Milan duration 5 -> implies exact 3-7

    # Direct flight descriptions (as provided)
    flight_descriptions = [
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
    adj = parse_flights(flight_descriptions)

    # Derive fixed city windows based on constraints
    fixed_windows: Dict[str, Tuple[int, int]] = {}

    # London fixed 1-3
    fixed_windows["London"] = london_show_days
    assert durations["London"] == london_show_days[1] - london_show_days[0] + 1

    # Milan: duration 5 and must include days 3-7 -> exactly 3-7
    milan_start, milan_end = milan_friends_window
    assert durations["Milan"] == milan_end - milan_start + 1
    fixed_windows["Milan"] = (milan_start, milan_end)

    # Zurich fixed 7-8
    fixed_windows["Zurich"] = zurich_conference_days
    assert durations["Zurich"] == zurich_conference_days[1] - zurich_conference_days[0] + 1

    # Reykjavik fixed 9-13
    fixed_windows["Reykjavik"] = reykjavik_relatives_days
    assert durations["Reykjavik"] == reykjavik_relatives_days[1] - reykjavik_relatives_days[0] + 1

    # Identify a 2-day bridge city between Zurich (end day 8) and Reykjavik (start day 9)
    two_day_cities = {c for c, d in durations.items() if d == 2}
    # Exclude Zurich and Reykjavik (already fixed), also exclude London (3 days)
    bridge_exclude = {"Zurich", "Reykjavik"}
    bridge_city = find_bridge_city_2days(adj, two_day_cities, "Zurich", "Reykjavik", bridge_exclude)
    if bridge_city is None:
        raise ValueError("No valid 2-day bridge city found between Zurich and Reykjavik with direct flights.")
    # We'll set bridge city to be exactly days 8-9
    fixed_windows[bridge_city] = (8, 9)

    # Build the initial ordered blocks with fixed windows in chronological order
    # Blocks must be ordered and ensure direct flights between consecutive cities on overlap day
    # Expected initial order: London (1-3) -> Milan (3-7) -> Zurich (7-8) -> bridge_city (8-9) -> Reykjavik (9-13)
    initial_order = ["London", "Milan", "Zurich", bridge_city, "Reykjavik"]

    # Validate direct flights for initial transitions
    for i in range(len(initial_order) - 1):
        a, b = initial_order[i], initial_order[i+1]
        assert b in adj.get(a, set()), f"No direct flight from {a} to {b}"

    # Remaining cities to schedule after Reykjavik
    remaining_cities = set(cities) - set(initial_order)

    # Find a path covering all remaining cities starting from any city that is directly reachable from Reykjavik
    rem_sequence = find_sequence_from_source("Reykjavik", remaining_cities, adj)
    if not rem_sequence:
        raise ValueError("Could not find a valid direct-flight sequence for the remaining cities.")

    # Now compute day ranges using overlapping-by-1 pattern
    # For fixed windows we already have exact days. We ensure continuity (end of block = start of next block)
    itinerary_blocks: List[Tuple[str, int, int]] = []

    # Append initial fixed blocks in order
    for city in initial_order:
        start, end = fixed_windows[city]
        itinerary_blocks.append((city, start, end))

    # Append remaining sequence, starting at previous end day
    current_end = itinerary_blocks[-1][2]  # end of Reykjavik, should be 13
    for city in rem_sequence:
        dur = durations[city]
        start = current_end  # overlap by 1 day
        end = start + dur - 1
        # Validate direct flight from previous city to this city
        prev_city = itinerary_blocks[-1][0]
        assert city in adj.get(prev_city, set()), f"No direct flight from {prev_city} to {city}"
        itinerary_blocks.append((city, start, end))
        current_end = end

    # Final validation: overall should cover exactly 28 days from Day 1 to Day 28
    assert itinerary_blocks[0][1] == 1, "Itinerary must start on Day 1"
    assert itinerary_blocks[-1][2] == total_days, f"Itinerary must end on Day {total_days}"

    # Validate each city's total days match durations and specific day requirements are included
    # Build a mapping of day -> set of cities present that day
    day_presence: Dict[int, Set[str]] = {day: set() for day in range(1, total_days + 1)}
    for city, start, end in itinerary_blocks:
        for d in range(start, end + 1):
            day_presence[d].add(city)

    # Count days per city
    city_day_counts = {c: 0 for c in cities}
    for day in range(1, total_days + 1):
        for c in day_presence[day]:
            city_day_counts[c] += 1

    # Check counts
    for c, d in durations.items():
        assert city_day_counts[c] == d, f"City {c} day count mismatch: expected {d}, got {city_day_counts[c]}"

    # Specific day constraints verification
    # London days 1-3
    for d in range(1, 4):
        assert "London" in day_presence[d], "London must be present days 1-3"
    # Zurich days 7-8
    for d in range(7, 9):
        assert "Zurich" in day_presence[d], "Zurich must be present days 7-8"
    # Reykjavik days 9-13
    for d in range(9, 14):
        assert "Reykjavik" in day_presence[d], "Reykjavik must be present days 9-13"
    # Milan includes days 3-7
    for d in range(3, 8):
        assert "Milan" in day_presence[d], "Milan must be present days 3-7"

    # Build output itinerary
    output_itinerary = []
    for city, start, end in itinerary_blocks:
        output_itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": output_itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))