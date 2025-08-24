import json
from collections import defaultdict

def build_adjacency(edges):
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def compress_itinerary(path):
    # path is list of loc[1..19]
    segments = []
    start = 1
    current = path[0]
    for i in range(1, len(path)):
        if path[i] != current:
            segments.append({"day_range": f"Day {start}-{i}", "place": current})
            start = i + 1
            current = path[i]
    segments.append({"day_range": f"Day {start}-{len(path)}", "place": current})
    return segments

def search_itinerary(cities, adj, req_days, event_days, total_days=19):
    # Backtracking over days 1..total_days
    # loc[d] = city for day d (1-indexed)
    required_total = dict(req_days)
    # For pruning: total required days
    total_required_days = sum(required_total.values())
    # Max presence slots over total_days is at most 2*total_days - 1? With this model, max per day is 2 (except day1 which is 1), so max = 1 + 2*(total_days-1) = 2*total_days - 1
    # But this is not strictly needed for pruning now.

    # Prepare fast list of cities needing days
    initial_counts = {c: 0 for c in cities}

    # Determine required city per event day (single city per day here)
    event_city_by_day = {}
    for day, reqset in event_days.items():
        # Take the single city required on this day
        # If multiple, keep set; but this scenario uses singletons
        event_city_by_day[day] = next(iter(reqset))

    # Heuristic: order of cities for branching
    def order_choices(day, prev, choices, counts):
        # Prefer choices that:
        # - satisfy event by making city equal to required city on this day (if prev != required)
        # - need more days (higher remaining)
        req_city = event_city_by_day.get(day)
        items = []
        for city in choices:
            rem = required_total[city] - counts[city]
            score = rem
            # prioritize exact event match
            if req_city is not None and prev != req_city and city == req_city:
                score += 1000
            # deprioritize cities already satisfied
            if rem <= 0:
                score -= 100
            items.append((score, city))
        items.sort(key=lambda x: (-x[0], x[1]))
        return [c for _, c in items]

    best_path = None
    visited_cache = set()  # cache states to avoid recomputation

    def backtrack(day, prev, counts, path):
        nonlocal best_path

        # If all days assigned
        if day > total_days:
            # Validate exact counts
            for c in cities:
                if counts[c] != required_total[c]:
                    return False
            best_path = list(path)
            return True

        # Build allowed choices for day
        if day == 1:
            # Presence on day 1 is only loc1; must satisfy event if any
            if 1 in event_city_by_day:
                choices = [event_city_by_day[1]]
            else:
                # If no event (not the case here), allow any city
                choices = list(cities)
        else:
            # Stay or move to neighbor (direct flight)
            choices = [prev] + sorted(adj[prev])

            # Enforce event: presence on day includes next and (if changed) prev
            if day in event_city_by_day:
                req_city = event_city_by_day[day]
                if prev == req_city:
                    # any choice is fine (presence will include prev)
                    pass
                else:
                    # must set next to req_city to include it in presence
                    if req_city in choices:
                        choices = [req_city]
                    else:
                        return False

        # Heuristic ordering
        choices = order_choices(day, prev, choices, counts)

        for city in choices:
            # Direct flight constraint is satisfied by construction for day>1.
            # Compute presence on this day
            presence = set([city])
            if day > 1 and city != prev:
                presence.add(prev)

            # Check event presence
            if day in event_city_by_day:
                req_city = event_city_by_day[day]
                if req_city not in presence:
                    continue

            # Update counts
            new_counts = counts.copy()
            exceeded = False
            for p in presence:
                new_counts[p] += 1
                if new_counts[p] > required_total[p]:
                    exceeded = True
                    break
            if exceeded:
                continue

            # Feasibility check: remaining days must be enough for each city
            remaining_days = total_days - day
            impossible = False
            for c in cities:
                rem_need = required_total[c] - new_counts[c]
                # On each remaining day, any city can be counted at most once
                if rem_need > remaining_days:
                    impossible = True
                    break
            if impossible:
                continue

            # Cache state to prune: (day, prev, tuple sorted counts? but prev matters; we include counts tuple)
            key = (day, prev if prev is not None else "_", city, tuple(new_counts[c] for c in cities))
            if key in visited_cache:
                continue
            visited_cache.add(key)

            # Recurse
            path.append(city)
            if backtrack(day + 1, city, new_counts, path):
                return True
            path.pop()

        return False

    # Initialize with day 1
    path = []
    # Start with no previous city; counts all zero
    backtrack(1, None, initial_counts, path)
    return best_path

def main():
    # Cities and constraints
    cities = [
        "Lisbon", "Dubrovnik", "Copenhagen", "Prague",
        "Tallinn", "Stockholm", "Split", "Lyon"
    ]

    required_days = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }

    # Direct flights (undirected)
    flight_pairs = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague"),
    ]
    adjacency = build_adjacency(flight_pairs)

    # Event constraints: day -> set of cities that must be present that day
    events = {
        1: {"Tallinn"},
        2: {"Tallinn"},
        4: {"Lisbon"},
        5: {"Lisbon"},
        13: {"Stockholm"},
        14: {"Stockholm"},
        15: {"Stockholm"},
        16: {"Stockholm"},
        18: {"Lyon"},
        19: {"Lyon"},
    }

    path = search_itinerary(cities, adjacency, required_days, events, total_days=19)

    if not path:
        # If no plan found, output empty itinerary
        output = {"itinerary": []}
    else:
        itinerary = compress_itinerary(path)
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()