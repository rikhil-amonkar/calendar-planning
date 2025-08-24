import itertools
import json

def main():
    # Input variables
    total_days = 8
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    desired_stays = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2,
    }
    direct_flights = [
        ("Stuttgart", "Split"),
        ("Prague", "Florence"),
        ("Krakow", "Stuttgart"),
        ("Krakow", "Split"),
        ("Split", "Prague"),
        ("Krakow", "Prague"),
    ]
    # Event constraints
    wedding_city = "Stuttgart"
    wedding_days = (2, 3)  # must be in Stuttgart on both day 2 and day 3
    friends_city = "Split"
    friends_days = (3, 4)  # must be in Split on both day 3 and day 4

    # Build adjacency set for undirected direct flights
    adjacency = set(tuple(sorted(p)) for p in direct_flights)

    def is_direct(a, b):
        return tuple(sorted((a, b))) in adjacency

    # Helper to build presence sets given a path and flight days
    def build_presence(path, flights):
        # segments (inclusive, overlapping at flight days):
        # C1: [1, f1]
        # C2: [f1, f2]
        # C3: [f2, f3]
        # C4: [f3, f4]
        # C5: [f4, total_days]
        presence = {city: set() for city in path}
        segment_bounds = []
        for i in range(len(path)):
            if i == 0:
                start = 1
            else:
                start = flights[i - 1]
            if i < len(flights):
                end = flights[i]
            else:
                end = total_days
            segment_bounds.append((start, end))

        # Fill presence sets
        for i, city in enumerate(path):
            start, end = segment_bounds[i]
            for d in range(start, end + 1):
                presence[city].add(d)

        return presence, segment_bounds

    # Verify constraints for a candidate schedule
    def valid_schedule(path, flights):
        # Direct flights only between consecutive cities
        for a, b in zip(path, path[1:]):
            if not is_direct(a, b):
                return False, None, None

        # Build presence and counts
        presence, segment_bounds = build_presence(path, flights)

        # Check exact stays
        for city in cities:
            if len(presence.get(city, set())) != desired_stays[city]:
                return False, None, None

        # Check event constraints
        w1, w2 = wedding_days
        if w1 not in presence[wedding_city] or w2 not in presence[wedding_city]:
            return False, None, None

        f1, f2 = friends_days
        if f1 not in presence[friends_city] or f2 not in presence[friends_city]:
            return False, None, None

        return True, presence, segment_bounds

    # Search for a feasible path and flight days
    solution = None
    # We need exactly len(cities)-1 flights to produce the required double counts
    num_flights = len(cities) - 1

    for path in itertools.permutations(cities):
        # Quick connectivity pruning: all consecutive pairs must be direct
        if any(not is_direct(a, b) for a, b in zip(path, path[1:])):
            continue

        for flights in itertools.combinations(range(1, total_days + 1), num_flights):
            ok, presence, segment_bounds = valid_schedule(path, flights)
            if ok:
                # Build itinerary as overlapping ranges per city segment
                itinerary = []
                for i, city in enumerate(path):
                    start, end = segment_bounds[i]
                    itinerary.append({
                        "day_range": f"Day {start}-{end}",
                        "place": city
                    })
                solution = {"itinerary": itinerary}
                print(json.dumps(solution, ensure_ascii=False))
                return

    # If no solution found (should not happen with the given constraints), output empty itinerary
    print(json.dumps({"itinerary": []}, ensure_ascii=False))

if __name__ == "__main__":
    main()