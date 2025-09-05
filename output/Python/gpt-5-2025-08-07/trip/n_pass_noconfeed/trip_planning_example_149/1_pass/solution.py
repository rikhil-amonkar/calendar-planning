import json
from collections import defaultdict

def solve_itinerary():
    # Input variables (trip constraints)
    total_days = 10
    cities = ["London", "Santorini", "Istanbul"]
    required_stays = {
        "London": 3,
        "Santorini": 6,
        "Istanbul": 3
    }
    direct_flights = [
        ("Istanbul", "London"),
        ("London", "Santorini")
    ]
    must_be_in_city_on_days = {
        "Santorini": {5, 10}
    }

    # Build adjacency (undirected graph of direct flights)
    adjacency = {c: set() for c in cities}
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)

    # Prepare must-be-in per day as a dict day -> set of cities required that day
    day_requirements = {d: set() for d in range(1, total_days + 1)}
    for city, days in must_be_in_city_on_days.items():
        for d in days:
            day_requirements[d].add(city)

    # Helper to check if a set of cities satisfies day requirements
    def valid_day_inclusions(day, inclusions):
        req = day_requirements.get(day, set())
        return req.issubset(inclusions)

    # DFS search with backtracking to find an itinerary with minimal flights
    best_solution = {
        "daily_inclusions": None,   # list index 1..total_days of sets of cities present that day
        "flight_days": None,        # list of day numbers where a flight occurred
        "flight_count": None
    }

    # For deterministic exploration
    city_order = ["Istanbul", "London", "Santorini"]
    for c in adjacency:
        adjacency[c] = sorted(adjacency[c], key=lambda x: city_order.index(x))

    def dfs(day, current_city, counts, daily_inclusions, flight_days, flight_count):
        nonlocal best_solution

        # Prune if counts already exceed required for any city
        for c in cities:
            if counts[c] > required_stays[c]:
                return

        # If we already have a solution, prune branches with equal or more flights
        if best_solution["flight_count"] is not None and flight_count > best_solution["flight_count"]:
            return

        # If all days assigned, check if counts match requirements exactly
        if day > total_days:
            # All must-be-in constraints are implicitly enforced day-by-day
            if all(counts[c] == required_stays[c] for c in cities):
                # Update best solution if fewer flights
                if (best_solution["flight_count"] is None) or (flight_count < best_solution["flight_count"]):
                    best_solution["daily_inclusions"] = [set(s) if isinstance(s, set) else set(s) for s in daily_inclusions]
                    best_solution["flight_days"] = list(flight_days)
                    best_solution["flight_count"] = flight_count
            return

        # Action 1: Stay in current city (no flight), inclusion is {current_city}
        inclusions = {current_city}
        if valid_day_inclusions(day, inclusions):
            # Update counts
            counts[current_city] += 1
            daily_inclusions[day] = set(inclusions)
            dfs(day + 1, current_city, counts, daily_inclusions, flight_days, flight_count)
            # Backtrack
            counts[current_city] -= 1
            daily_inclusions[day] = set()

        # Action 2: Fly to a neighbor city (direct flight) -> inclusion is {current_city, neighbor}
        for neighbor in adjacency[current_city]:
            inclusions = {current_city, neighbor}
            if not valid_day_inclusions(day, inclusions):
                continue
            # Update counts (both cities get the day)
            counts[current_city] += 1
            counts[neighbor] += 1
            daily_inclusions[day] = set(inclusions)
            flight_days.append(day)
            dfs(day + 1, neighbor, counts, daily_inclusions, flight_days, flight_count + 1)
            # Backtrack
            flight_days.pop()
            counts[current_city] -= 1
            counts[neighbor] -= 1
            daily_inclusions[day] = set()

    # Try starting from each city; order chosen to increase chance of minimal flights satisfying constraints
    for start_city in ["Istanbul", "London", "Santorini"]:
        counts_init = {c: 0 for c in cities}
        daily_inclusions_init = [set() for _ in range(total_days + 1)]  # index 0 unused
        flight_days_init = []
        dfs(1, start_city, counts_init, daily_inclusions_init, flight_days_init, 0)
        # If found a solution with the theoretical minimum flights equal to the extra day credits needed, we can stop
        # Extra day credits needed = sum(required) - total_days
        extra_credit = sum(required_stays.values()) - total_days
        if best_solution["flight_count"] is not None and best_solution["flight_count"] == max(0, extra_credit):
            break

    # If no solution found, return empty itinerary
    if best_solution["daily_inclusions"] is None:
        return {"itinerary": []}

    # Build aggregated itinerary as day ranges per city (allowing overlaps on flight days)
    inclusions_by_day = best_solution["daily_inclusions"]

    def compress_ranges(days_list):
        if not days_list:
            return []
        days_list = sorted(days_list)
        ranges = []
        start = prev = days_list[0]
        for d in days_list[1:]:
            if d == prev + 1:
                prev = d
            else:
                ranges.append((start, prev))
                start = prev = d
        ranges.append((start, prev))
        return ranges

    # Collect day lists for each city
    city_day_ranges = []
    for city in cities:
        days_in_city = [d for d in range(1, total_days + 1) if city in inclusions_by_day[d]]
        ranges = compress_ranges(days_in_city)
        for (s, e) in ranges:
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            city_day_ranges.append((s, {"day_range": day_range_str, "place": city}))

    # Sort by starting day for readability
    city_day_ranges.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in city_day_ranges]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))