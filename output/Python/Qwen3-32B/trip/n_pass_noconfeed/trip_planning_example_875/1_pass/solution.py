import itertools
import json

def main():
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    durations = {
        'Stuttgart': 3,
        'Edinburgh': 4,
        'Athens': 4,
        'Split': 2,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 4
    }

    direct_flights_input = [
        ("Krakow", "Split"),
        ("Split", "Athens"),
        ("Edinburgh", "Krakow"),
        ("Venice", "Stuttgart"),
        ("Krakow", "Stuttgart"),
        ("Edinburgh", "Stuttgart"),
        ("Stuttgart", "Athens"),
        ("Split", "Stuttgart"),
        ("Edinburgh", "Athens"),
        ("Athens", "Mykonos"),
        ("Venice", "Edinburgh"),
        ("Venice", "Athens"),
        ("Stuttgart", "Split"),
        ("Edinburgh", "Athens"),
    ]

    direct_flights_set = set()
    for a, b in direct_flights_input:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))

    for perm in itertools.permutations(cities):
        valid_transitions = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in direct_flights_set:
                valid_transitions = False
                break
        if not valid_transitions:
            continue

        # Compute start days
        start_days = [0] * len(perm)
        start_days[0] = 1
        for i in range(1, len(perm)):
            start_days[i] = start_days[i-1] + durations[perm[i-1]] - 1

        # Check constraints
        # Stuttgart
        stuttgart_idx = perm.index('Stuttgart')
        stuttgart_start = start_days[stuttgart_idx]
        stuttgart_end = stuttgart_start + durations['Stuttgart'] - 1
        workshop_valid = any(stuttgart_start <= d <= stuttgart_end for d in [11, 12, 13])

        if not workshop_valid:
            continue

        # Split
        split_idx = perm.index('Split')
        split_start = start_days[split_idx]
        split_end = split_start + durations['Split'] - 1
        split_valid = any(split_start <= d <= split_end for d in [13, 14])

        if not split_valid:
            continue

        # Krakow
        krakow_idx = perm.index('Krakow')
        krakow_start = start_days[krakow_idx]
        krakow_end = krakow_start + durations['Krakow'] - 1
        krakow_valid = any(krakow_start <= d <= krakow_end for d in range(8, 12))

        if not krakow_valid:
            continue

        # Build itinerary
        itinerary = []
        for i in range(len(perm)):
            city = perm[i]
            duration = durations[city]
            start = start_days[i]
            end = start + duration - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        print(json.dumps({"itinerary": itinerary}))
        return

if __name__ == "__main__":
    main()