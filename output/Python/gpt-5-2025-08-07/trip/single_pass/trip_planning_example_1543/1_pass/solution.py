import json
from itertools import permutations

def build_adjacency(pairs):
    adj = {}
    for a, b in pairs:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def has_edge(adj, a, b):
    return b in adj.get(a, set())

def compute_itinerary():
    total_days = 26

    # Trip requirements: durations (in days) for each city
    durations = {
        "Prague": 3,
        "London": 3,
        "Lisbon": 5,
        "Seville": 2,
        "Athens": 3,
        "Dubrovnik": 3,
        "Dublin": 3,
        "Porto": 5,
        "Warsaw": 4,
        "Vilnius": 4,
    }

    # Must-be-present windows (inclusive)
    windows = {
        "Prague": (1, 3),   # Workshop days 1-3
        "London": (3, 5),   # Wedding days 3-5
        "Lisbon": (5, 9),   # Relatives days 5-9
        "Porto": (16, 20),  # Conference days 16-20
        "Warsaw": (20, 23), # Friends meet days 20-23
    }

    # Direct flights (undirected)
    flight_pairs = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens"),
    ]
    adjacency = build_adjacency(flight_pairs)

    # Pre-fixed order due to hard windows and total continuity
    prefix = ["Prague", "London", "Lisbon"]
    suffix = ["Porto", "Warsaw", "Vilnius"]
    all_cities = list(durations.keys())
    flexible = [c for c in all_cities if c not in prefix + suffix]  # should be 4 cities

    best_itinerary = None

    for perm in permutations(flexible):
        path = prefix + list(perm) + suffix

        # Check direct flight connectivity along the path
        if not all(has_edge(adjacency, path[i], path[i+1]) for i in range(len(path)-1)):
            continue

        # Build day ranges sequentially with overlap on travel days
        day_ranges = {}
        valid = True
        for i, city in enumerate(path):
            if i == 0:
                s = 1
            else:
                s = day_ranges[path[i-1]][1]  # Overlap on travel day
            e = s + durations[city] - 1
            day_ranges[city] = (s, e)

            # Check windows: the city's block must include its required window
            if city in windows:
                wstart, wend = windows[city]
                if not (s <= wstart <= e and s <= wend <= e):
                    valid = False
                    break
                # If duration equals the window length, enforce exact match
                if durations[city] == (wend - wstart + 1):
                    if not (s == wstart and e == wend):
                        valid = False
                        break

        if not valid:
            continue

        # Ensure the schedule spans exactly the required total days
        first_city = path[0]
        last_city = path[-1]
        if day_ranges[first_city][0] != 1:
            continue
        if day_ranges[last_city][1] != total_days:
            continue

        # All constraints satisfied; construct itinerary list
        itinerary = []
        for city in path:
            s, e = day_ranges[city]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

        best_itinerary = itinerary
        break

    if best_itinerary is None:
        # Fallback: no valid plan found (should not happen with given constraints)
        return {"itinerary": []}

    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))