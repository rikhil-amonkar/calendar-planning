import itertools
import json

def build_flight_graph(cities):
    graph = {c: set() for c in cities}
    def add_bidirectional(a, b):
        graph[a].add(b)
        graph[b].add(a)
    def add_directed(a, b):
        graph[a].add(b)

    # Direct flights list (as per constraints)
    add_bidirectional("Prague", "Tallinn")
    add_bidirectional("Prague", "Zurich")
    add_bidirectional("Florence", "Prague")
    add_bidirectional("Frankfurt", "Bucharest")
    add_bidirectional("Frankfurt", "Venice")
    add_bidirectional("Prague", "Bucharest")
    add_bidirectional("Bucharest", "Zurich")
    add_bidirectional("Tallinn", "Frankfurt")
    add_directed("Zurich", "Florence")  # directed
    add_bidirectional("Frankfurt", "Zurich")
    add_bidirectional("Zurich", "Venice")
    add_bidirectional("Florence", "Frankfurt")
    add_bidirectional("Prague", "Frankfurt")
    add_bidirectional("Tallinn", "Zurich")
    return graph

def intersects(a_start, a_end, b_start, b_end):
    return not (a_end < b_start or b_end < a_start)

def compute_schedule(order, durations, total_days):
    # Build contiguous segments where next start equals previous end (travel day counts for both)
    schedule = []
    start = 1
    for city in order:
        end = start + durations[city] - 1
        schedule.append((city, start, end))
        start = end  # next segment starts on the same day (travel day overlap)
    if schedule[-1][2] != total_days:
        return None
    return schedule

def validate_order(order, graph, durations, windows, total_days):
    # Check direct flights between consecutive cities
    for i in range(len(order) - 1):
        if order[i+1] not in graph[order[i]]:
            return False, None

    # Build schedule
    schedule = compute_schedule(order, durations, total_days)
    if schedule is None:
        return False, None

    # Windows must intersect
    city_to_range = {city: (s, e) for city, s, e in schedule}
    for city, (w_start, w_end) in windows.items():
        s, e = city_to_range[city]
        if not intersects(s, e, w_start, w_end):
            return False, None

    return True, schedule

def main():
    total_days = 26
    durations = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5,
    }
    cities = list(durations.keys())

    # Sanity: sum of durations must equal total_days + (segments - 1) for a feasible chain with overlaps
    if sum(durations.values()) != total_days + (len(cities) - 1):
        raise ValueError("Durations do not align with total days and overlap rule.")

    graph = build_flight_graph(cities)

    # Time windows: must be present in these cities on at least one day in the given ranges (inclusive)
    windows = {
        "Venice": (22, 26),     # Wedding window
        "Frankfurt": (12, 16),  # Annual show window
        "Tallinn": (8, 12),     # Friends meetup window
    }

    # Search for a feasible itinerary
    best_schedule = None
    for order in itertools.permutations(cities):
        valid, schedule = validate_order(order, graph, durations, windows, total_days)
        if valid:
            best_schedule = schedule
            break

    if not best_schedule:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    # Format output
    itinerary = []
    for city, s, e in best_schedule:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()