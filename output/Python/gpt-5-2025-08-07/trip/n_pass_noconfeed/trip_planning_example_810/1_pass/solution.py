import itertools
import json
from collections import defaultdict

def build_adjacency(edges):
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def is_path_connected(order, adj):
    for i in range(len(order) - 1):
        if order[i+1] not in adj[order[i]]:
            return False
    return True

def compute_schedule(order, durations, total_days):
    # Compute start and end days for each city with overlap on transition days
    schedule = {}
    start = 1
    for i, city in enumerate(order):
        if i == 0:
            s = start
        else:
            # overlap day with previous city's end day
            s = schedule[order[i-1]][1]
        e = s + durations[city] - 1
        schedule[city] = (s, e)
    # Validate total calendar days equals total_days
    last_city = order[-1]
    if schedule[last_city][1] != total_days:
        return None
    return schedule

def events_satisfied(schedule, events):
    for city, days in events.items():
        if city not in schedule:
            return False
        s, e = schedule[city]
        for d in days:
            if not (s <= d <= e):
                return False
    return True

def ranges_to_itinerary(schedule, order):
    itinerary = []
    for city in order:
        s, e = schedule[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
    return itinerary

def main():
    # Input variables (constraints)
    total_days = 20
    durations = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2
    }
    direct_flights = [
        ("Lyon", "Nice"),
        ("Stockholm", "Athens"),
        ("Nice", "Athens"),
        ("Berlin", "Athens"),
        ("Berlin", "Nice"),
        ("Berlin", "Barcelona"),
        ("Berlin", "Vilnius"),
        ("Barcelona", "Nice"),
        ("Athens", "Vilnius"),
        ("Berlin", "Stockholm"),
        ("Nice", "Stockholm"),
        ("Barcelona", "Athens"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Lyon")
    ]
    # Mandatory presence events
    events = {
        "Berlin": {1, 3},        # conference on day 1 and day 3
        "Barcelona": {3, 4},     # workshop between day 3 and day 4 (present on both)
        "Lyon": {4, 5}           # wedding between day 4 and day 5 (present on both)
    }

    # Basic feasibility check
    cities = list(durations.keys())
    if sum(durations.values()) - (len(cities) - 1) != total_days:
        # If this ever happens, the durations cannot fit into total_days with direct overlaps only
        print(json.dumps({"error": "Durations do not match total days given overlap rules."}))
        return

    adj = build_adjacency(direct_flights)

    # Generate candidate orders:
    # Must start in Berlin to satisfy day 1 presence
    start_city = "Berlin"
    other_cities = [c for c in cities if c != start_city]

    best_order = None
    best_schedule = None

    # Search permutations and select the first valid itinerary that satisfies constraints
    for perm in itertools.permutations(other_cities):
        order = [start_city] + list(perm)
        # Connectivity (direct flights between consecutive cities)
        if not is_path_connected(order, adj):
            continue
        # Compute schedule (with overlaps) and ensure it exactly fills the calendar
        schedule = compute_schedule(order, durations, total_days)
        if schedule is None:
            continue
        # Check mandatory day events
        if not events_satisfied(schedule, events):
            continue
        # Found a valid itinerary
        best_order = order
        best_schedule = schedule
        break

    if best_order is None or best_schedule is None:
        print(json.dumps({"error": "No feasible itinerary found that satisfies all constraints."}))
        return

    itinerary = ranges_to_itinerary(best_schedule, best_order)
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()