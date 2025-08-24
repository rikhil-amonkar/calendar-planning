import json
from collections import defaultdict

def build_adjacency(direct_pairs):
    adj = defaultdict(set)
    for a, b in direct_pairs:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def compute_itinerary():
    total_days = 24

    # Trip constraints (inputs)
    required_days = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5,
    }

    windows = [
        ("Munich", 4, 6),      # Attend show
        ("Santorini", 8, 10),  # Visit relatives
        ("Valencia", 14, 15),  # Workshop
    ]

    direct_pairs = [
        ("Bucharest", "Manchester"),
        ("Munich", "Venice"),
        ("Santorini", "Manchester"),
        ("Vienna", "Reykjavik"),
        ("Venice", "Santorini"),
        ("Munich", "Porto"),
        ("Valencia", "Vienna"),
        ("Manchester", "Vienna"),
        ("Porto", "Vienna"),
        ("Venice", "Manchester"),
        ("Santorini", "Vienna"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Bucharest", "Valencia"),
        ("Venice", "Vienna"),
        ("Bucharest", "Vienna"),
        ("Porto", "Manchester"),
        ("Munich", "Vienna"),
        ("Valencia", "Porto"),
        ("Munich", "Bucharest"),
        ("Tallinn", "Munich"),
        ("Santorini", "Bucharest"),
        ("Munich", "Valencia"),
    ]
    adj = build_adjacency(direct_pairs)

    # Target total city-days determines required number of flights
    sum_required = sum(required_days.values())
    required_flights = sum_required - total_days
    if required_flights < 0:
        raise ValueError("Infeasible: required days sum less than total days.")

    # Construct a feasible plan (derived logically from constraints)
    # end_city_by_day specifies which city you end each day in (flight occurs on that day if changed from day-1)
    plan_end_city = {
        1: "Tallinn",
        2: "Tallinn",
        3: "Tallinn",
        4: "Munich",      # Flight: Tallinn -> Munich
        5: "Munich",
        6: "Venice",      # Flight: Munich -> Venice
        7: "Venice",
        8: "Santorini",   # Flight: Venice -> Santorini
        9: "Santorini",
        10: "Manchester", # Flight: Santorini -> Manchester
        11: "Manchester",
        12: "Porto",      # Flight: Manchester -> Porto
        13: "Porto",
        14: "Valencia",   # Flight: Porto -> Valencia
        15: "Bucharest",  # Flight: Valencia -> Bucharest (keeps Valencia at exactly 2 days)
        16: "Bucharest",
        17: "Bucharest",
        18: "Bucharest",
        19: "Vienna",     # Flight: Bucharest -> Vienna
        20: "Vienna",
        21: "Vienna",
        22: "Vienna",
        23: "Reykjavik",  # Flight: Vienna -> Reykjavik
        24: "Reykjavik",
    }

    # Validate adjacency on flight days and build per-day presence
    end_city = [None] * (total_days + 1)  # 1-indexed; end_city[0] will mirror day 1
    for d in range(1, total_days + 1):
        end_city[d] = plan_end_city[d]
    end_city[0] = end_city[1]

    flights = []
    per_day_places = []
    for d in range(1, total_days + 1):
        prev_c = end_city[d - 1]
        curr_c = end_city[d]
        if curr_c != prev_c:
            if curr_c not in adj[prev_c]:
                raise ValueError(f"No direct flight on Day {d}: {prev_c} -> {curr_c}")
            flights.append((d, prev_c, curr_c))
            places = [prev_c, curr_c]
        else:
            places = [curr_c]
        per_day_places.append((d, places))

    # Count city-days
    city_counts = defaultdict(int)
    for _, places in per_day_places:
        for c in places:
            city_counts[c] += 1

    # Validate required days per city (exact match)
    for city, req in required_days.items():
        got = city_counts.get(city, 0)
        if got != req:
            raise ValueError(f"City {city} requires {req} days but got {got}")

    # Validate windows presence
    for city, start, end in windows:
        for d in range(start, end + 1):
            _, places = per_day_places[d - 1]
            if city not in places:
                raise ValueError(f"Window violation: must be in {city} on Day {d}")

    # Validate total flights count
    if len(flights) != required_flights:
        raise ValueError(f"Flight count mismatch: expected {required_flights}, got {len(flights)}")

    # Build JSON itinerary: list of day mappings with places present (to reflect flight-day overlaps)
    itinerary = []
    for d, places in per_day_places:
        itinerary.append({"day": f"Day {d}", "places": places})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))