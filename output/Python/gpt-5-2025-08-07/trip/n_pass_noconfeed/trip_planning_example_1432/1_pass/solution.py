import json
from itertools import permutations

def build_graph():
    graph = {}
    def add_city(c):
        if c not in graph:
            graph[c] = set()
    def add_undirected(a, b):
        add_city(a); add_city(b)
        graph[a].add(b)
        graph[b].add(a)
    def add_directed(a, b):
        add_city(a); add_city(b)
        graph[a].add(b)

    # Cities
    cities = [
        "Valencia","Frankfurt","Vienna","Bucharest","Athens","Riga",
        "Stockholm","Amsterdam","Reykjavik","Salzburg"
    ]
    for c in cities:
        add_city(c)

    # Build edges from the provided statements
    add_undirected("Valencia", "Frankfurt")
    add_undirected("Vienna", "Bucharest")
    add_directed("Valencia", "Athens")
    add_undirected("Athens", "Bucharest")
    add_undirected("Riga", "Frankfurt")
    add_undirected("Stockholm", "Athens")
    add_undirected("Amsterdam", "Bucharest")
    add_directed("Athens", "Riga")
    add_undirected("Amsterdam", "Frankfurt")
    add_undirected("Stockholm", "Vienna")
    add_undirected("Vienna", "Riga")
    add_undirected("Amsterdam", "Reykjavik")
    add_undirected("Reykjavik", "Frankfurt")
    add_undirected("Stockholm", "Amsterdam")
    add_undirected("Amsterdam", "Valencia")
    add_undirected("Vienna", "Frankfurt")
    add_undirected("Valencia", "Vienna")
    add_undirected("Bucharest", "Frankfurt")
    add_undirected("Stockholm", "Frankfurt")
    add_directed("Reykjavik", "Athens")
    add_undirected("Frankfurt", "Salzburg")
    add_undirected("Amsterdam", "Vienna")
    add_undirected("Stockholm", "Reykjavik")
    add_undirected("Amsterdam", "Riga")
    add_undirected("Stockholm", "Riga")
    add_undirected("Vienna", "Reykjavik")
    add_undirected("Amsterdam", "Athens")
    add_undirected("Athens", "Frankfurt")
    add_undirected("Vienna", "Athens")
    add_undirected("Riga", "Bucharest")

    return graph

def main():
    # Input variables (constraints)
    total_days = 29
    required_stays = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 5,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 3
    }

    # Event windows (fixed placements)
    # These are fixed due to explicit day constraints
    anchored_blocks = [
        {"city": "Stockholm", "start": 1, "end": 3},     # meet friend between day 1 and 3; 3 days total
        {"city": "Valencia", "start": 5, "end": 6},      # show day 5-6; 2 days total
        {"city": "Vienna", "start": 6, "end": 10},       # wedding between day 6 and 10; 5 days total
        {"city": "Athens", "start": 14, "end": 18},      # workshop between day 14 and 18; 5 days total
        {"city": "Riga", "start": 18, "end": 20},        # conference day 18-20; 3 days total
    ]

    graph = build_graph()

    # Helper for checking directed connectivity
    def has_edge(a, b):
        return (a in graph) and (b in graph[a])

    # Sort anchored blocks by start day
    anchored_blocks.sort(key=lambda x: x["start"])

    # Fill inter-anchored gaps with suitable cities and verify direct flight edges
    scheduled = {blk["city"]: (blk["start"], blk["end"]) for blk in anchored_blocks}

    # Function to find a city to fill a specific gap, ensuring directed edges
    def find_city_for_gap(prev_city, next_city, length, already_used):
        candidates = []
        for city, dur in required_stays.items():
            if city in already_used:
                continue
            if dur != length:
                continue
            # Must have prev_city -> city on gap start day and city -> next_city on gap end day
            if has_edge(prev_city, city) and has_edge(city, next_city):
                candidates.append(city)
        if not candidates:
            return None
        # If multiple, choose arbitrarily (deterministically by sorted name)
        candidates.sort()
        return candidates[0]

    # Build list of blocks including filled gaps
    blocks = []
    for i in range(len(anchored_blocks)-1):
        curr = anchored_blocks[i]
        nxt = anchored_blocks[i+1]
        blocks.append(curr)
        # gap occurs if next.start > curr.end
        if nxt["start"] > curr["end"]:
            gap_start = curr["end"]
            gap_end = nxt["start"]
            gap_length = gap_end - gap_start + 1
            prev_city = curr["city"]
            next_city = nxt["city"]
            city = find_city_for_gap(prev_city, next_city, gap_length, already_used=set([b["city"] for b in blocks] + [nxt["city"]]))
            if city is None:
                raise RuntimeError(f"No city found to fill gap between {prev_city} (end {curr['end']}) and {next_city} (start {nxt['start']}) of length {gap_length}")
            blocks.append({"city": city, "start": gap_start, "end": gap_end})
    # Append the last anchored block
    blocks.append(anchored_blocks[-1])

    # Determine remaining cities not scheduled yet
    used_cities = set(b["city"] for b in blocks)
    remaining_cities = [c for c in required_stays if c not in used_cities]

    # After the last anchored block (Riga 18-20), fill the remaining days to reach day 29
    last_block = blocks[-1]
    assert last_block["city"] == "Riga" and last_block["end"] == 20, "Last anchored block should be Riga ending on day 20"

    # Find a feasible chain ordering for remaining cities that respects directed edges
    # We seek a chain starting at Riga where each transition is a direct flight.
    # The durations of remaining are fixed: Bucharest(3), Frankfurt(4), Salzburg(5).
    feasible_chain = None
    for order in permutations(remaining_cities):
        ok = True
        prev_city = last_block["city"]
        for city in order:
            if not has_edge(prev_city, city):
                ok = False
                break
            prev_city = city
        if ok:
            feasible_chain = order
            break
    if feasible_chain is None:
        raise RuntimeError("No feasible chain found for remaining cities after Riga")

    # Schedule the remaining chain with overlaps (start at last_block.end)
    current_start = last_block["end"]
    for city in feasible_chain:
        dur = required_stays[city]
        start = current_start
        end = start + dur - 1
        blocks.append({"city": city, "start": start, "end": end})
        current_start = end  # next block starts on this end day (flight overlap)

    # Sort all blocks by start day
    blocks.sort(key=lambda x: (x["start"], x["end"], x["city"]))

    # Validation: ensure all cities scheduled exactly once
    cities_in_blocks = [b["city"] for b in blocks]
    if len(set(cities_in_blocks)) != len(cities_in_blocks):
        raise RuntimeError("A city appears multiple times in the itinerary, which is not allowed for this plan.")

    # Validation: durations match required stays
    for b in blocks:
        city = b["city"]
        dur = b["end"] - b["start"] + 1
        if dur != required_stays[city]:
            raise RuntimeError(f"Duration for {city} is {dur}, expected {required_stays[city]}")

    # Validation: transitions are direct flights
    for i in range(len(blocks)-1):
        a = blocks[i]
        b = blocks[i+1]
        # Consecutive blocks must share a boundary day (flight day), i.e., a.end == b.start
        if a["end"] != b["start"]:
            raise RuntimeError(f"Blocks do not align on a flight day between {a['city']} (end {a['end']}) and {b['city']} (start {b['start']})")
        if not has_edge(a["city"], b["city"]):
            raise RuntimeError(f"No direct flight from {a['city']} to {b['city']}")

    # Validation: cover days 1..29 (unique days)
    covered_days = set()
    for b in blocks:
        covered_days.update(range(b["start"], b["end"]+1))
    if min(covered_days) != 1 or max(covered_days) != total_days or len(covered_days) != total_days:
        raise RuntimeError("The itinerary does not cover exactly days 1 through 29 uniquely (with overlaps only on flight days).")

    # Validation: event windows
    # Stockholm friend (days 1-3): already exactly days 1-3
    # Valencia show (days 5-6): exactly days 5-6
    # Vienna wedding (days 6-10): exactly days 6-10
    # Athens workshop (days 14-18): exactly days 14-18
    # Riga conference (days 18-20): exactly days 18-20
    must_blocks = {
        "Stockholm": (1,3),
        "Valencia": (5,6),
        "Vienna": (6,10),
        "Athens": (14,18),
        "Riga": (18,20)
    }
    for b in blocks:
        city = b["city"]
        if city in must_blocks:
            if (b["start"], b["end"]) != must_blocks[city]:
                raise RuntimeError(f"{city} must be scheduled as {must_blocks[city]}, got {(b['start'], b['end'])}")

    # Build output
    itinerary = []
    for b in blocks:
        itinerary.append({
            "day_range": f"Day {b['start']}-{b['end']}",
            "place": b["city"]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()