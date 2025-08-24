import json
import itertools

def build_flight_graph():
    # Build directed adjacency from the given direct flights list
    edges = {}
    def add_edge(a,b):
        edges.setdefault(a,set()).add(b)
    def add_undirected(a,b):
        add_edge(a,b)
        add_edge(b,a)
    # Given direct flights:
    add_undirected("Venice", "Madrid")
    add_undirected("Lisbon", "Reykjavik")
    add_undirected("Brussels", "Venice")
    add_undirected("Venice", "Santorini")
    add_undirected("Lisbon", "Venice")
    add_edge("Reykjavik", "Madrid")  # directional as stated
    add_undirected("Brussels", "London")
    add_undirected("Madrid", "London")
    add_undirected("Santorini", "London")
    add_undirected("London", "Reykjavik")
    add_undirected("Brussels", "Lisbon")
    add_undirected("Lisbon", "London")
    add_undirected("Lisbon", "Madrid")
    add_undirected("Madrid", "Santorini")
    add_undirected("Brussels", "Reykjavik")
    add_undirected("Brussels", "Madrid")
    add_undirected("Venice", "London")
    return edges

def has_flight(graph, a, b):
    return b in graph.get(a, set())

def compute_itinerary():
    total_days = 17

    # Required cities with required day counts (preferences treated as exact in this plan)
    durations = {
        "Venice": 3,
        "London": 3,
        "Lisbon": 4,
        "Brussels": 2,
        "Reykjavik": 3,
        "Santorini": 3,
        "Madrid": 5,
    }

    # Hard windows that must be covered (inclusive), deduced from constraints
    # We interpret "between day X and day Y" as inclusive of both endpoints.
    windows = {
        "Brussels": (1, 2),   # Must be in Brussels on Day 1-2
        "Venice":   (5, 7),   # Relatives Day 5-7
        "Madrid":   (7, 11),  # Wedding Day 7-11
    }

    cities = list(durations.keys())
    flights = build_flight_graph()

    # Validate window lengths match required durations for those cities
    for city, (s, e) in windows.items():
        if durations[city] != (e - s + 1):
            raise ValueError(f"Window length for {city} does not match required duration.")

    # Schedule fixed blocks first in chronological order with overlap rule
    # Block format: (city, start_day, end_day)
    blocks = []
    # 1) Brussels fixed
    blocks.append(("Brussels", windows["Brussels"][0], windows["Brussels"][1]))

    # 2) Determine the city that must sit between Brussels (ends day 2) and Venice (starts day 5)
    # Because flights overlap day, this city must occupy Days 2-5 (inclusive), i.e., 4 days
    pre_venice_start = windows["Brussels"][1]  # Day 2
    venice_start = windows["Venice"][0]        # Day 5
    needed_len = venice_start - pre_venice_start + 1  # 5 - 2 + 1 = 4

    remaining_after_fixed = set(cities) - set(windows.keys())
    pre_venice_candidates = [
        c for c in remaining_after_fixed
        if durations[c] == needed_len
        and has_flight(flights, "Brussels", c)
        and has_flight(flights, c, "Venice")
    ]

    if not pre_venice_candidates:
        raise RuntimeError("No city can fit the required pre-Venice slot with direct flights.")
    # If multiple, pick the first (there should be only Lisbon)
    pre_venice_city = pre_venice_candidates[0]
    blocks.append((pre_venice_city, pre_venice_start, pre_venice_start + durations[pre_venice_city] - 1))

    # 3) Venice fixed (must start at day 5 due to overlap)
    venice_start_calc = blocks[-1][2]  # previous block's end day
    if venice_start_calc != windows["Venice"][0]:
        raise RuntimeError("Pre-Venice city does not align to start Venice on the required day.")
    blocks.append(("Venice", windows["Venice"][0], windows["Venice"][1]))

    # 4) Madrid fixed (must start day 7, end day 11)
    madrid_start_calc = blocks[-1][2]  # Day 7
    if madrid_start_calc != windows["Madrid"][0]:
        raise RuntimeError("Venice block does not align to start Madrid on the required day.")
    blocks.append(("Madrid", windows["Madrid"][0], windows["Madrid"][1]))

    # 5) Remaining three cities to place after Madrid (Days 11-17).
    remaining_cities = list(remaining_after_fixed - {pre_venice_city})
    # We need an order perm = [C5, C6, C7] such that:
    # - direct flight Madrid -> C5
    # - direct flight C5 -> C6
    # - direct flight C6 -> C7
    # and day ranges fit exactly:
    #   C5: 11-13 (3 days), C6: 13-15 (3 days), C7: 15-17 (3 days)
    post_madrid_orders = []
    for perm in itertools.permutations(remaining_cities, 3):
        if has_flight(flights, "Madrid", perm[0]) \
           and has_flight(flights, perm[0], perm[1]) \
           and has_flight(flights, perm[1], perm[2]):
            post_madrid_orders.append(perm)

    if not post_madrid_orders:
        raise RuntimeError("No feasible ordering of remaining cities with direct flights after Madrid.")

    chosen_order = post_madrid_orders[0]

    # Assign day ranges for the last three blocks with overlap
    c5, c6, c7 = chosen_order
    c5_start = blocks[-1][2]  # Day 11
    c5_end = c5_start + durations[c5] - 1  # Day 13
    blocks.append((c5, c5_start, c5_end))

    c6_start = c5_end  # Day 13
    c6_end = c6_start + durations[c6] - 1  # Day 15
    blocks.append((c6, c6_start, c6_end))

    c7_start = c6_end  # Day 15
    c7_end = c7_start + durations[c7] - 1  # Day 17
    blocks.append((c7, c7_start, c7_end))

    # Final validations:
    # - Check all cities covered exactly once
    block_cities = [b[0] for b in blocks]
    if set(block_cities) != set(cities) or len(blocks) != len(cities):
        raise RuntimeError("City coverage mismatch in blocks.")

    # - Check durations match
    for city, s, e in blocks:
        if e - s + 1 != durations[city]:
            raise RuntimeError(f"Duration mismatch for {city}: expected {durations[city]}, got {e - s + 1}")

    # - Check windows contained (inclusive)
    for city, (ws, we) in windows.items():
        # City block must include the required window
        blk = next((b for b in blocks if b[0] == city), None)
        if not blk:
            raise RuntimeError(f"Missing block for window city {city}")
        s, e = blk[1], blk[2]
        if not (s <= ws <= e and s <= we <= e):
            raise RuntimeError(f"Window for {city} not contained in its block.")

    # - Check flights between consecutive blocks (using day-overlap rule)
    for i in range(len(blocks) - 1):
        a_city = blocks[i][0]
        b_city = blocks[i + 1][0]
        if not has_flight(build_flight_graph(), a_city, b_city):
            raise RuntimeError(f"No direct flight from {a_city} to {b_city}")

    # - Check calendar span equals total_days (first day = 1, last day = 17)
    if blocks[0][1] != 1 or blocks[-1][2] != total_days:
        raise RuntimeError("Calendar span does not match required total days.")

    # Prepare output
    itinerary = []
    for city, s, e in blocks:
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))