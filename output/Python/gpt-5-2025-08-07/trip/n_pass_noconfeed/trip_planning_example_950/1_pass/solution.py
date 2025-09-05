import json
from itertools import permutations

def build_graph():
    # Build adjacency with both undirected ("and") and directed ("from ... to ...") edges
    adj = {}
    def add_node(x):
        if x not in adj:
            adj[x] = set()
    def add_undirected(a, b):
        add_node(a); add_node(b)
        adj[a].add(b); adj[b].add(a)
    def add_directed(a, b):
        add_node(a); add_node(b)
        adj[a].add(b)

    # Undirected connections ("and")
    add_undirected("Nice", "Riga")
    add_undirected("Bucharest", "Munich")
    add_undirected("Mykonos", "Munich")
    add_undirected("Riga", "Bucharest")
    add_undirected("Rome", "Nice")
    add_undirected("Rome", "Munich")
    add_undirected("Mykonos", "Nice")
    add_undirected("Rome", "Mykonos")
    add_undirected("Munich", "Krakow")
    add_undirected("Rome", "Bucharest")
    add_undirected("Nice", "Munich")

    # Directed connections ("from ... to ...")
    add_directed("Riga", "Munich")
    add_directed("Rome", "Riga")

    return adj

def has_edge(adj, a, b):
    return b in adj.get(a, set())

def find_city_order(adj, cities, durations, total_days, anchors):
    # Required cities and durations
    # Anchors specify fixed presence: Rome on day 1 and 4; Mykonos on day 4-6; Krakow on day 16-17
    start_city = "Rome"
    wedding_city = "Mykonos"
    end_city = "Krakow"

    # Must start in Rome, then go to Mykonos on day 4 (to be in both Rome and Mykonos on day 4)
    # We'll keep this ordering prefix fixed: [Rome, Mykonos, ... , Krakow]
    remaining = [c for c in cities if c not in [start_city, wedding_city, end_city]]

    # We must end in Munich before Krakow due to direct flight constraint (only Munich-Krakow is given)
    # So ensure the last city before Krakow is Munich
    if "Munich" not in remaining:
        raise ValueError("Munich must be in the remaining cities list.")
    # Generate permutations where the last is Munich
    mids = [c for c in remaining if c != "Munich"]
    for perm in permutations(mids):
        candidate_order = [start_city, wedding_city] + list(perm) + ["Munich", end_city]
        # Check direct flights between consecutive cities
        ok = True
        for i in range(len(candidate_order)-1):
            if not has_edge(adj, candidate_order[i], candidate_order[i+1]):
                ok = False
                break
        if not ok:
            continue
        # Check that calendar days will fit: sum(required) - (moves between cities) == total_days
        # Moves between cities = len(candidate_order) - 1
        total_required = sum(durations[c] for c in candidate_order)
        moves = len(candidate_order) - 1
        if total_required - moves == total_days:
            return candidate_order
    raise RuntimeError("No feasible city order satisfying direct flights and day constraints.")

def build_schedule(adj, order, durations, total_days):
    # Compute "primary" days per city:
    # For all cities except the last (Krakow), primary_days = required - 1 (because departure day adds 1)
    # For the last city, primary_days = required (no outgoing flight day to add)
    end_city = order[-1]
    primary_needed = {city: (durations[city] if city == end_city else durations[city] - 1) for city in order}

    primary_by_day = {}  # day -> primary city
    presence = {city: set() for city in order}  # city -> set of days present (including flight overlap days)
    flights = []  # list of (day, from, to)

    day = 1

    # Assign primary days for first city (no prior arrival flight day)
    first = order[0]
    for _ in range(primary_needed[first]):
        if day > total_days:
            raise RuntimeError("Ran out of days while assigning first city.")
        primary_by_day[day] = first
        presence[first].add(day)
        day += 1

    # Iterate through subsequent cities with flight days
    for i in range(len(order)-1):
        src = order[i]
        dst = order[i+1]
        if not has_edge(adj, src, dst):
            raise RuntimeError(f"No direct flight from {src} to {dst}.")

        # Flight day: counts for both src and dst, and primary city = dst
        if day > total_days:
            raise RuntimeError("Ran out of days when scheduling flights.")
        flights.append((day, src, dst))
        presence[src].add(day)
        presence[dst].add(day)
        primary_by_day[day] = dst
        day += 1

        # Assign remaining primary days for dst (excluding the arrival/flight day already counted)
        remaining_primary = primary_needed[dst] - 1
        for _ in range(remaining_primary):
            if day > total_days:
                raise RuntimeError("Ran out of days while assigning destination primary days.")
            primary_by_day[day] = dst
            presence[dst].add(day)
            day += 1

    if day != total_days + 1:
        raise RuntimeError("Schedule did not exactly fill the total number of days.")

    return primary_by_day, presence, flights

def compress_itinerary(primary_by_day):
    # Compress contiguous days with the same primary city into ranges
    days = sorted(primary_by_day.keys())
    segments = []
    if not days:
        return segments
    start = days[0]
    end = days[0]
    city = primary_by_day[start]

    for d in days[1:]:
        if primary_by_day[d] == city and d == end + 1:
            end = d
        else:
            segments.append((start, end, city))
            start = d
            end = d
            city = primary_by_day[d]
    segments.append((start, end, city))

    itinerary = []
    for s, e, c in segments:
        if s == e:
            dr = f"Day {s}"
        else:
            dr = f"Day {s}-{e}"
        itinerary.append({"day_range": dr, "place": c})
    return itinerary

def validate_plan(presence, durations, anchors, flights, order):
    # Validate durations per city
    for city, req in durations.items():
        actual = len(presence.get(city, set()))
        if actual != req:
            raise RuntimeError(f"Duration mismatch for {city}: required {req}, got {actual}")

    # Validate anchors (must be present on specified days)
    for city, days in anchors.items():
        for d in days:
            if d not in presence.get(city, set()):
                raise RuntimeError(f"Anchor constraint failed: not in {city} on day {d}")

    # Validate moves are exactly between given cities in order
    for i, (day, src, dst) in enumerate(flights):
        if order[i] != src or order[i+1] != dst:
            raise RuntimeError("Flight order does not match city order.")

def main():
    total_days = 17
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    # Required exact day counts per city (including flight-overlap days)
    durations = {
        "Mykonos": 3,
        "Riga": 3,
        "Munich": 4,
        "Bucharest": 4,
        "Rome": 4,
        "Nice": 3,
        "Krakow": 2
    }
    # Anchors: fixed days where presence is required
    anchors = {
        "Rome": {1, 4},
        "Mykonos": {4, 5, 6},
        "Krakow": {16, 17}
    }

    # Build direct flights graph
    adj = build_graph()

    # Find a feasible city order that respects direct flights and total day math
    order = find_city_order(adj, cities, durations, total_days, anchors)

    # Build the detailed schedule with primary days and presence accounting for flight overlaps
    primary_by_day, presence, flights = build_schedule(adj, order, durations, total_days)

    # Validate constraints (durations and anchors)
    validate_plan(presence, durations, anchors, flights, order)

    # Compress to day-range itinerary by primary city
    itinerary = compress_itinerary(primary_by_day)

    # Output the result as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()