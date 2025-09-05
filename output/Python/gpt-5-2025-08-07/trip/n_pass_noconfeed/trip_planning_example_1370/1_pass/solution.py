import json

def parse_flights(text):
    # Build directed adjacency from flight description text
    adj = {}
    def add_edge(a, b):
        adj.setdefault(a, set()).add(b)

    items = [itm.strip() for itm in text.strip().split(",")]
    for raw in items:
        if not raw:
            continue
        s = raw.strip()
        if s.endswith("."):
            s = s[:-1].strip()
        if s.lower().startswith("from "):
            # from X to Y
            s2 = s[5:].strip()  # remove 'from '
            if " to " not in s2:
                continue
            a, b = [x.strip() for x in s2.split(" to ", 1)]
            add_edge(a, b)
        elif " and " in s:
            a, b = [x.strip() for x in s.split(" and ", 1)]
            add_edge(a, b)
            add_edge(b, a)
    return adj

def find_itinerary(cities, durations, windows, adj, total_days=30):
    # Backtracking search to find an order that:
    # - uses direct flights between consecutive cities
    # - matches durations exactly
    # - matches window constraints (arrival and departure days) for specified cities
    # Travel day counts as a day in both cities:
    # arrival_day(next_city) = departure_day(prev_city)
    # departure_day(city) = arrival_day + duration(city) - 1
    all_cities = list(cities)

    # Pre-calc for pruning: cities with windows
    window_cities = set(windows.keys())

    def valid_transition(a, b):
        return b in adj.get(a, set())

    target_sum = sum(durations[c] for c in cities)
    # Sanity check: total unique days must be target_sum - (num_cities-1)
    if target_sum - (len(cities) - 1) != total_days:
        # If this doesn't hold, no solution exists under single-visit assumption
        return None

    best_order = []

    def backtrack(order, last_depart_day, used):
        nonlocal best_order

        idx = len(order)
        if idx == 0:
            arrival_next = 1
        else:
            arrival_next = last_depart_day

        if idx == len(all_cities):
            # All cities placed; verify we end exactly on total_days
            if last_depart_day == total_days:
                best_order = order[:]
                return True
            return False

        # Remaining cities to try
        remaining = [c for c in all_cities if c not in used]

        # Small heuristic: try cities with windows earlier to prune search
        remaining.sort(key=lambda c: (0 if c in window_cities else 1, c))

        for city in remaining:
            # adjacency check
            if idx > 0 and not valid_transition(order[-1], city):
                continue

            # compute this city's arrival and departure
            arrival = arrival_next
            depart = arrival + durations[city] - 1

            # window check
            if city in windows:
                want_arrival, want_depart = windows[city]
                if arrival != want_arrival or depart != want_depart:
                    continue

            # Must not exceed total_days if this is the last city
            if idx == len(all_cities) - 1:
                if depart != total_days:
                    continue
            else:
                # Intermediate city should depart strictly before or equal to total_days,
                # but can be equal because next city's arrival equals this depart.
                if depart > total_days:
                    continue

            used.add(city)
            order.append((city, arrival, depart))
            if backtrack(order, depart, used):
                return True
            order.pop()
            used.remove(city)

        return False

    found = backtrack([], None, set())
    if not found:
        return None

    # Build itinerary structure
    itinerary = []
    for city, start, end in best_order:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    return itinerary

def main():
    # Input variables
    total_days = 30
    cities = [
        "Santorini",
        "Krakow",
        "Paris",
        "Vilnius",
        "Munich",
        "Geneva",
        "Amsterdam",
        "Budapest",
        "Split",
    ]
    durations = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }
    # Windows: exact arrival and departure days required
    windows = {
        "Paris": (11, 15),
        "Krakow": (18, 22),
        "Santorini": (25, 29),
    }
    flights_text = """
    Paris and Krakow, Paris and Amsterdam, Paris and Split, from Vilnius to Munich, Paris and Geneva,
    Amsterdam and Geneva, Munich and Split, Split and Krakow, Munich and Amsterdam, Budapest and Amsterdam,
    Split and Geneva, Vilnius and Split, Munich and Geneva, Munich and Krakow, from Krakow to Vilnius,
    Vilnius and Amsterdam, Budapest and Paris, Krakow and Amsterdam, Vilnius and Paris, Budapest and Geneva,
    Split and Amsterdam, Santorini and Geneva, Amsterdam and Santorini, Munich and Budapest, Munich and Paris.
    """

    adj = parse_flights(flights_text)

    itinerary = find_itinerary(set(cities), durations, windows, adj, total_days=total_days)
    if itinerary is None:
        # If no itinerary found, output empty structure
        output = {"itinerary": []}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()