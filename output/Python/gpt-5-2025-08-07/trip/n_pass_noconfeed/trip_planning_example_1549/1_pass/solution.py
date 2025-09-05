import json
from typing import List, Dict, Tuple, Set

def parse_direct_flights(flight_statements: List[str]) -> Dict[str, Set[str]]:
    adj = {}
    def add_city(c):
        if c not in adj:
            adj[c] = set()
    def add_edge(a, b):
        add_city(a); add_city(b)
        adj[a].add(b)

    for raw in flight_statements:
        s = raw.strip().rstrip(",.")
        if not s:
            continue
        if s.lower().startswith("from "):
            # Pattern: from A to B
            parts = s.split()
            # Expect "from", "<A...>", "to", "<B...>"
            try:
                idx_to = parts.index("to")
            except ValueError:
                # Try lowercase "to"
                idx_to = parts.index("to")
            a = " ".join(parts[1:idx_to])
            b = " ".join(parts[idx_to+1:])
            add_edge(a, b)
        elif " and " in s:
            a, b = s.split(" and ")
            a = a.strip()
            b = b.strip()
            add_edge(a, b)
            add_edge(b, a)
        else:
            # Fallback: ignore malformed
            pass
    return adj

def compute_day_ranges(order: List[str], durations: Dict[str, int]) -> List[Dict[str, str]]:
    itinerary = []
    # First city starts at Day 1, ends at 1 + d - 1
    start_day = 1
    for i, city in enumerate(order):
        d = durations[city]
        if i == 0:
            city_start = start_day
        else:
            # On a flight day, both cities count, so next start equals previous end
            city_start = itinerary[-1]["_end"]
        city_end = city_start + d - 1
        itinerary.append({
            "day_range": f"Day {city_start}-{city_end}",
            "place": city,
            "_start": city_start,
            "_end": city_end
        })
    # Remove helper keys
    for x in itinerary:
        x.pop("_start", None)
        x.pop("_end", None)
    return itinerary

def verify_constraints(
    itinerary_blocks: List[Dict[str, str]],
    order: List[str],
    durations: Dict[str, int],
    total_days: int,
    anchors: Dict[str, Tuple[int, int]],
    adj: Dict[str, Set[str]]
):
    # Recompute start/end numeric from strings for verification
    parsed = []
    for block in itinerary_blocks:
        dr = block["day_range"].replace("Day ", "")
        a, b = dr.split("-")
        parsed.append((block["place"], int(a), int(b)))

    # 1) Durations match requested
    for city, s, e in parsed:
        assert (e - s + 1) == durations[city], f"Duration mismatch for {city}"

    # 2) Overlap rule implies total unique days equals end of last block
    assert parsed[-1][2] == total_days, f"Total days mismatch: got {parsed[-1][2]}, expected {total_days}"

    # 3) Anchors satisfied: each city range must include anchor window fully
    for city, (a_start, a_end) in anchors.items():
        found = [p for p in parsed if p[0] == city]
        assert len(found) == 1, f"City {city} must appear exactly once"
        _, s, e = found[0]
        assert s <= a_start <= e and s <= a_end <= e, f"Anchor for {city} not satisfied: needed {a_start}-{a_end}, scheduled {s}-{e}"

    # 4) Direct flights adjacency (directional)
    for i in range(len(order) - 1):
        a = order[i]
        b = order[i + 1]
        assert a in adj and b in adj[a], f"No direct flight from {a} to {b}"

    # 5) Count of cities equals 10
    assert len(order) == 10, f"Expected 10 cities, got {len(order)}"

def main():
    # Input variables (constraints)
    total_days = 28
    city_durations = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2,
    }
    anchors = {
        "Riga": (5, 8),      # Attend annual show on days 5-8
        "Tallinn": (18, 20), # Visit relatives on days 18-20
        "Milan": (24, 26),   # Meet friend on days 24-26
    }

    # Direct flights, with "and" meaning bidirectional, "from A to B" meaning directional A->B
    direct_flights_raw = [
        "Riga and Prague",
        "Stockholm and Milan",
        "Riga and Milan",
        "Lisbon and Stockholm",
        "from Stockholm to Santorini",
        "Naples and Warsaw",
        "Lisbon and Warsaw",
        "Naples and Milan",
        "Lisbon and Naples",
        "from Riga to Tallinn",
        "Tallinn and Prague",
        "Stockholm and Warsaw",
        "Riga and Warsaw",
        "Lisbon and Riga",
        "Riga and Stockholm",
        "Lisbon and Porto",
        "Lisbon and Prague",
        "Milan and Porto",
        "Prague and Milan",
        "Lisbon and Milan",
        "Warsaw and Porto",
        "Warsaw and Tallinn",
        "Santorini and Milan",
        "Stockholm and Prague",
        "Stockholm and Tallinn",
        "Warsaw and Milan",
        "Santorini and Naples",
        "Warsaw and Prague",
    ]
    adj = parse_direct_flights(direct_flights_raw)

    # Determine a sequence of 10 cities that satisfies anchors and direct flights,
    # while meeting all stay-duration requirements and using exactly 9 flights.
    #
    # Strategy:
    # - Start in a city with 5-day stay and direct flight to Riga so we can arrive Riga on Day 5.
    # - Prefer Lisbon over Prague at start to avoid needing to revisit Prague (Tallinn connects directly to Prague post-Day 20).
    # - Chain from Riga to Tallinn via cities with direct connections and required durations:
    #   Riga -> Stockholm -> Santorini -> Naples -> Warsaw -> Tallinn
    # - After Tallinn, go to Prague (direct) to satisfy its 5-day stay,
    #   then to Milan for friend days 24-26, then to Porto to finish.
    first_anchor_start = anchors["Riga"][0]  # Day 5
    candidate_starts = []
    for city, dur in city_durations.items():
        if dur == first_anchor_start and "Riga" in adj.get(city, set()):
            candidate_starts.append(city)
    # Prefer Lisbon if available; else fallback to any candidate
    start_city = None
    if "Lisbon" in candidate_starts:
        start_city = "Lisbon"
    elif candidate_starts:
        start_city = candidate_starts[0]
    else:
        raise RuntimeError("No valid start city with 5-day stay and direct flight to Riga")

    # Construct order
    proposed_order = [
        start_city,      # Days 1-5
        "Riga",          # Days 5-8
        "Stockholm",     # Days 8-9
        "Santorini",     # Days 9-13
        "Naples",        # Days 13-17
        "Warsaw",        # Days 17-18
        "Tallinn",       # Days 18-20
        "Prague",        # Days 20-24
        "Milan",         # Days 24-26
        "Porto",         # Days 26-28
    ]

    # Ensure all required cities are included exactly once
    required_cities = set(city_durations.keys())
    assert set(proposed_order) == required_cities, "Proposed order does not include exactly the required 10 cities"

    # Verify adjacency for proposed order
    for i in range(len(proposed_order) - 1):
        a = proposed_order[i]
        b = proposed_order[i + 1]
        if b not in adj.get(a, set()):
            raise RuntimeError(f"No direct flight from {a} to {b}; cannot build itinerary")

    # Compute day ranges using overlap rule (flight day counts for both consecutive cities)
    itinerary_blocks = []
    start_day = 1
    for idx, city in enumerate(proposed_order):
        d = city_durations[city]
        if idx == 0:
            s = start_day
        else:
            s = itinerary_blocks[-1]["_end"]  # overlap on flight day
        e = s + d - 1
        itinerary_blocks.append({"place": city, "day_range": f"Day {s}-{e}", "_start": s, "_end": e})

    # Final verification of constraints
    # Create a clean version of itinerary for output
    output_itinerary = [{"day_range": b["day_range"], "place": b["place"]} for b in itinerary_blocks]

    verify_constraints(output_itinerary, proposed_order, city_durations, total_days, anchors, adj)

    # Output JSON
    print(json.dumps({"itinerary": output_itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()