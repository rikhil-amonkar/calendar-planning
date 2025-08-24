import json
import itertools

def build_adjacency(direct_pairs):
    adj = {}
    for a, b in direct_pairs:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def is_connected_path(order, adjacency):
    return all(order[i+1] in adjacency.get(order[i], set()) for i in range(len(order)-1))

def compute_intervals(order, stay_requirements, total_days):
    n = len(order)
    # Sum of required stays must equal total_days + (n-1) because each of the (n-1) flight days count for both cities.
    if sum(stay_requirements[c] for c in order) != total_days + (n - 1):
        return None
    ranges = []
    for i, city in enumerate(order):
        if i == 0:
            start = 1
        else:
            # Overlap 1 day with previous segment to account for flight day counting for both cities.
            start = ranges[-1][1]
        end = start + stay_requirements[city] - 1
        ranges.append((start, end, city))
    # Ensure the last day matches total_days
    if ranges[-1][1] != total_days:
        return None
    return ranges

def intersects(a_start, a_end, b_start, b_end):
    return max(a_start, b_start) <= min(a_end, b_end)

def satisfies_event(ranges, event_city, event_window):
    for start, end, city in ranges:
        if city == event_city:
            if intersects(start, end, event_window[0], event_window[1]):
                return True
    return False

def format_itinerary(ranges):
    return [{"day_range": f"Day {start}-{end}", "place": city} for start, end, city in ranges]

def main():
    # Input variables (constraints)
    total_days = 16
    cities = ["Bucharest", "Lyon", "Porto"]
    stay_requirements = {
        "Bucharest": 7,
        "Lyon": 7,
        "Porto": 4
    }
    # Direct flights (undirected)
    direct_flights = [("Bucharest", "Lyon"), ("Lyon", "Porto")]
    adjacency = build_adjacency(direct_flights)
    event_city = "Bucharest"
    event_window = (1, 7)  # inclusive day range

    # Generate feasible routes that respect direct-flight connectivity
    feasible_routes = []
    for order in itertools.permutations(cities):
        if is_connected_path(order, adjacency):
            ranges = compute_intervals(order, stay_requirements, total_days)
            if ranges and satisfies_event(ranges, event_city, event_window):
                feasible_routes.append(ranges)

    # Choose an "optimal" solution: here, the first feasible one found
    if feasible_routes:
        chosen = feasible_routes[0]
        itinerary = format_itinerary(chosen)
    else:
        itinerary = []

    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()