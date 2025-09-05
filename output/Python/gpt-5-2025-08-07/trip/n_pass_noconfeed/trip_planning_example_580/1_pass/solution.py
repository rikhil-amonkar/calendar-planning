import json
from itertools import permutations

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 23
    cities = ["Paris", "Oslo", "Porto", "Geneva", "Reykjavik"]
    durations = {
        "Paris": 6,
        "Oslo": 5,
        "Porto": 7,
        "Geneva": 7,
        "Reykjavik": 2
    }
    # Special constraints
    conference_city = "Geneva"
    conference_days = {1, 7}  # Must be in Geneva on days 1 and 7
    oslo_visit_range = (19, 23)  # Must be in Oslo days 19-23 inclusive

    # Direct flights (undirected)
    given_edges = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo"),
    ]
    direct_edges = set(frozenset(edge) for edge in given_edges)

    def has_direct(a, b):
        return frozenset({a, b}) in direct_edges

    # We must start in Geneva on Day 1 and be there Day 7; simplest is Geneva first block of 7 days
    start_city = "Geneva"
    end_city = "Oslo"

    middle_cities = [c for c in cities if c not in (start_city, end_city)]

    best_route = None
    best_schedule = None

    # Try all permutations of middle cities and find a valid route that satisfies direct flights
    for perm in permutations(middle_cities):
        route = [start_city] + list(perm) + [end_city]

        # Check adjacency connections (direct flights)
        if not all(has_direct(route[i], route[i+1]) for i in range(len(route)-1)):
            continue

        # Build schedule with overlap on travel days:
        # If you fly from A to B on day X, you are in both on day X => next block starts at prev end day
        schedule = {}  # city -> (start_day, end_day)
        current_day_start = 1
        for city in route:
            city_len = durations[city]
            city_end = current_day_start + city_len - 1
            schedule[city] = (current_day_start, city_end)
            current_day_start = city_end  # Next city starts on the same day (overlap travel day)

        # Validate calendar end
        final_end = schedule[route[-1]][1]
        if final_end != total_days:
            continue

        # Validate special constraints
        # Geneva presence days: must include days 1 and 7
        g_start, g_end = schedule[conference_city]
        if not (g_start <= 1 <= g_end and g_start <= 7 <= g_end):
            continue

        # Oslo must be days 19-23
        o_start, o_end = schedule[end_city]
        if not (o_start == oslo_visit_range[0] and o_end == oslo_visit_range[1]):
            continue

        # Validate durations match
        if any((schedule[c][1] - schedule[c][0] + 1) != durations[c] for c in cities):
            continue

        # Validate total city-day sum equals total_days + (number of transitions)
        total_city_days = sum(durations.values())
        expected = total_days + (len(route) - 1)
        if total_city_days != expected:
            continue

        # If multiple valid routes exist, choose the first (or could implement other optimal criteria)
        best_route = route
        best_schedule = schedule
        break

    if best_route is None or best_schedule is None:
        raise ValueError("No valid itinerary found with the given constraints and direct flights.")

    # Build output itinerary in chronological order of the route
    itinerary = []
    for city in best_route:
        start, end = best_schedule[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))