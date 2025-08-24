import itertools
import json

def build_adjacency(connections, cities):
    adj = {c: set() for c in cities}
    for conn in connections:
        conn = conn.strip()
        if " from " in conn or conn.lower().startswith("from "):
            # handle "from A to B"
            # normalize possible formats like "from Zurich to Florence"
            parts = conn.lower().replace("from ", "").split(" to ")
            if len(parts) == 2:
                a = parts[0].strip().title()
                b = parts[1].strip().title()
                if a in adj:
                    adj[a].add(b)
        elif " and " in conn:
            a, b = [p.strip().title() for p in conn.split(" and ")]
            if a in adj:
                adj[a].add(b)
            if b in adj:
                adj[b].add(a)
    return adj

def compute_itinerary(sequence, durations):
    # Build day ranges with 1-day overlaps between consecutive cities
    itinerary = []
    start = 1
    for i, city in enumerate(sequence):
        length = durations[city]
        end = start + length - 1
        itinerary.append((city, start, end))
        start = end  # next city starts on the same day (overlap)
    return itinerary

def intersects(a_start, a_end, b_start, b_end):
    return not (a_end < b_start or a_start > b_end)

def valid_sequence(seq, durations, adj, total_days, constraints):
    # Check direct flights
    for a, b in zip(seq, seq[1:]):
        if b not in adj.get(a, set()):
            return False

    # Compute itinerary
    it_list = compute_itinerary(seq, durations)

    # Check total days end
    if it_list[-1][2] != total_days:
        return False

    # Check per-city duration correctness (implicit by construction)

    # Apply constraints:
    # Frankfurt must fully cover days 12-16
    fr_city = "Frankfurt"
    fr_block = next((s, e) for city, s, e in it_list if city == fr_city)
    if not (fr_block[0] == constraints["frankfurt_show"][0] and fr_block[1] == constraints["frankfurt_show"][1]):
        return False

    # Tallinn must intersect [8,12]
    tl_city = "Tallinn"
    tl_block = next((s, e) for city, s, e in it_list if city == tl_city)
    if not intersects(tl_block[0], tl_block[1], constraints["tallinn_friends"][0], constraints["tallinn_friends"][1]):
        return False

    # Venice must intersect [22,26]
    ve_city = "Venice"
    ve_block = next((s, e) for city, s, e in it_list if city == ve_city)
    if not intersects(ve_block[0], ve_block[1], constraints["venice_wedding"][0], constraints["venice_wedding"][1]):
        return False

    return True

def main():
    # Input variables (constraints)
    total_days = 26
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]

    durations = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5,
    }

    connections = [
        "Prague and Tallinn",
        "Prague and Zurich",
        "Florence and Prague",
        "Frankfurt and Bucharest",
        "Frankfurt and Venice",
        "Prague and Bucharest",
        "Bucharest and Zurich",
        "Tallinn and Frankfurt",
        "from Zurich to Florence",
        "Frankfurt and Zurich",
        "Zurich and Venice",
        "Florence and Frankfurt",
        "Prague and Frankfurt",
        "Tallinn and Zurich",
    ]

    constraints = {
        "frankfurt_show": (12, 16),  # must be in Frankfurt for all these days
        "tallinn_friends": (8, 12),  # be in Tallinn at least one day within this window
        "venice_wedding": (22, 26),  # be in Venice at least one day within this window
    }

    adj = build_adjacency(connections, cities)

    # We'll search permutations. To make search deterministic and efficient,
    # we start from a plausible ordering; permutations will be lexicographic based on this order.
    base_order = ["Florence", "Prague", "Tallinn", "Frankfurt", "Bucharest", "Zurich", "Venice"]

    solution = None
    for seq in itertools.permutations(base_order):
        if valid_sequence(seq, durations, adj, total_days, constraints):
            # Build final itinerary output
            it_blocks = compute_itinerary(seq, durations)
            itinerary = []
            for city, start, end in it_blocks:
                itinerary.append({
                    "day_range": f"Day {start}-{end}",
                    "place": city
                })
            solution = {"itinerary": itinerary}
            break

    if solution is None:
        raise RuntimeError("No valid itinerary found under given constraints.")

    print(json.dumps(solution, ensure_ascii=False))

if __name__ == "__main__":
    main()