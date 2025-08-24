import json
import itertools
from collections import defaultdict

def compute_itinerary(total_days, required_stays, connections, required_presence):
    # Build undirected graph of direct flight connections
    graph = defaultdict(set)
    for a, b in connections:
        graph[a].add(b)
        graph[b].add(a)

    cities = list(required_stays.keys())
    num_cities = len(cities)
    # The number of flights (transition days) required to satisfy overlapping day counts
    flights_needed = sum(required_stays.values()) - total_days
    if flights_needed != (num_cities - 1):
        return None  # Impossible to satisfy with the given number of cities/days

    # Try all orders of visiting the cities that are connected by direct flights
    for order in itertools.permutations(cities):
        # Check direct-flight connectivity along the order
        ok_edges = all(order[i+1] in graph[order[i]] for i in range(len(order)-1))
        if not ok_edges:
            continue

        # Compute segment boundaries using inclusive overlap logic:
        # segment i: [start_i, end_i], with start_0 = 1, end_i = start_i + req_i - 1,
        # and start_{i+1} = end_i (flight day overlaps).
        boundaries = {}
        start_day = 1
        feasible = True
        for i, city in enumerate(order):
            req = required_stays[city]
            end_day = start_day + req - 1
            boundaries[city] = (start_day, end_day)
            start_day = end_day  # next city starts on the same day (flight day overlap)

        # Ensure the final city ends on total_days
        last_city = order[-1]
        if boundaries[last_city][1] != total_days:
            feasible = False

        # Ensure required presence constraints (e.g., being in Krakow on specific days)
        if feasible:
            for city, days in required_presence.items():
                if city not in boundaries:
                    feasible = False
                    break
                s, e = boundaries[city]
                for d in days:
                    if not (s <= d <= e):
                        feasible = False
                        break
                if not feasible:
                    break

        if feasible:
            # Build itinerary list in chronological order with overlapping day ranges
            itinerary = []
            for city in order:
                s, e = boundaries[city]
                itinerary.append({
                    "day_range": f"Day {s}-{e}",
                    "place": city
                })
            return {"itinerary": itinerary}

    return None

if __name__ == "__main__":
    # Input variables (constraints)
    total_days = 10
    required_stays = {
        "Krakow": 2,
        "Dubrovnik": 7,
        "Frankfurt": 3
    }
    # Direct flights available (undirected)
    connections = [
        ("Frankfurt", "Krakow"),
        ("Dubrovnik", "Frankfurt")
    ]
    # Must be in Krakow on days 9 and 10 (wedding)
    required_presence = {
        "Krakow": [9, 10]
    }

    result = compute_itinerary(total_days, required_stays, connections, required_presence)
    if result is None:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
    else:
        print(json.dumps(result))