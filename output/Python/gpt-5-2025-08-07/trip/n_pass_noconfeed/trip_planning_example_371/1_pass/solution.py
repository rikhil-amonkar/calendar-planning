import json
from collections import defaultdict

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 9
    cities = ["Vienna", "Nice", "Stockholm", "Split"]
    required_days = {
        "Vienna": 2,
        "Nice": 2,
        "Stockholm": 5,
        "Split": 3,
    }
    # Days (1-indexed) on which you must be in a specific city (can be present due to flight or stay)
    # Workshop in Vienna between day 1 and day 2 => must be in Vienna on days 1 and 2
    must_be_in = {
        1: {"Vienna"},
        2: {"Vienna"},
        7: {"Split"},  # Conference in Split on day 7
        9: {"Split"},  # Conference in Split on day 9
    }
    # Direct flights (undirected)
    direct_flights = [
        ("Vienna", "Nice"),
        ("Nice", "Stockholm"),
        ("Vienna", "Stockholm"),
        ("Vienna", "Split"),
        ("Stockholm", "Split"),
    ]

    # Build adjacency list for direct flights
    adj = defaultdict(list)
    for a, b in direct_flights:
        adj[a].append(b)
        adj[b].append(a)
    # Sort neighbors for determinism (optional)
    for k in adj:
        adj[k] = sorted(adj[k])

    # Calculate how many flight days are necessary:
    # Each flight day counts for both origin and destination (adds +1 extra city-day).
    # Sum(required_days) = base days (total_days) + number of flight days
    total_required_city_days = sum(required_days.values())
    required_flights = total_required_city_days - total_days
    if required_flights < 0 or required_flights > total_days:
        raise ValueError("Infeasible constraints for flights vs days.")

    # DFS search over days with constraints
    N = total_days

    def feasible_future(counts_after, day, flights_used_after):
        # Prune if any city already exceeds its required days
        for c in cities:
            if counts_after[c] > required_days[c]:
                return False
        # Ensure remaining days are enough to meet remaining per-city counts
        remaining_days = N - day
        for c in cities:
            rem_need = required_days[c] - counts_after[c]
            if rem_need < 0:
                return False
            if rem_need > remaining_days:
                return False
        # Ensure remaining days suffice for remaining flights (at most one per day)
        flights_remaining = required_flights - flights_used_after
        if flights_remaining < 0 or flights_remaining > remaining_days:
            return False
        return True

    def search(day, end_city, flights_used, presence_per_day, counts):
        if day > N:
            # End condition: exact match on flights and required days
            if flights_used == required_flights and all(counts[c] == required_days[c] for c in cities):
                return presence_per_day
            return None

        req_today = must_be_in.get(day, set())

        # Option 1: No flight today (stay in end_city)
        if len(req_today) <= 1 and (not req_today or end_city in req_today):
            presence = {end_city}
            # Update counts
            new_counts = counts.copy()
            new_counts[end_city] += 1
            # Feasibility check
            if feasible_future(new_counts, day, flights_used):
                presence_per_day[day] = presence
                res = search(day + 1, end_city, flights_used, presence_per_day, new_counts)
                if res is not None:
                    return res
                del presence_per_day[day]  # backtrack

        # Option 2: Take a direct flight today from end_city to any neighbor
        for dest in adj[end_city]:
            presence = {end_city, dest}
            # Must satisfy "must_be_in" cities today
            if not req_today.issubset(presence):
                continue
            new_counts = counts.copy()
            new_counts[end_city] += 1
            new_counts[dest] += 1
            new_flights_used = flights_used + 1
            if feasible_future(new_counts, day, new_flights_used):
                presence_per_day[day] = presence
                res = search(day + 1, dest, new_flights_used, presence_per_day, new_counts)
                if res is not None:
                    return res
                del presence_per_day[day]  # backtrack

        return None

    # Initialize day 1: must be Vienna (workshop constraint)
    presence_per_day = {}
    counts_init = {c: 0 for c in cities}
    presence_per_day[1] = {"Vienna"}
    counts_init["Vienna"] += 1
    start_city = "Vienna"
    flights_used_init = 0

    # Quick feasibility before starting recursion
    if not feasible_future(counts_init, 1, flights_used_init):
        raise ValueError("Initial constraints infeasible.")

    solution = search(2, start_city, flights_used_init, presence_per_day, counts_init)
    if solution is None:
        raise ValueError("No feasible itinerary found under given constraints.")

    # Convert daily presence into ranges per city
    def ranges_for_city(city, presence_map):
        days = [d for d in range(1, N + 1) if city in presence_map.get(d, set())]
        if not days:
            return []
        ranges = []
        start = days[0]
        prev = days[0]
        for d in days[1:]:
            if d == prev + 1:
                prev = d
            else:
                ranges.append((start, prev))
                start = d
                prev = d
        ranges.append((start, prev))
        return ranges

    all_entries = []
    for city in cities:
        for a, b in ranges_for_city(city, solution):
            all_entries.append({
                "start_day": a,
                "end_day": b,
                "place": city
            })

    # Sort by start_day for a clean chronological itinerary
    all_entries.sort(key=lambda x: (x["start_day"], x["end_day"], x["place"]))

    # Format as requested: "Day X-Y"
    itinerary_output = []
    for e in all_entries:
        itinerary_output.append({
            "day_range": f"Day {e['start_day']}-{e['end_day']}",
            "place": e["place"]
        })

    return {"itinerary": itinerary_output}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))