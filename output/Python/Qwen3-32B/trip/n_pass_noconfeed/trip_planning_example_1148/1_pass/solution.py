import itertools
import json

def main():
    cities = ['Tallinn', 'Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Stockholm', 'Split', 'Lyon']
    durations = {
        'Tallinn': 2,
        'Lisbon': 2,
        'Dubrovnik': 5,
        'Copenhagen': 5,
        'Prague': 3,
        'Stockholm': 4,
        'Split': 3,
        'Lyon': 2,
    }

    direct_flights = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Dubrovnik', 'Stockholm', 'Split', 'Prague', 'Lisbon', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Copenhagen', 'Split'],
        'Tallinn': ['Stockholm', 'Copenhagen'],
        'Stockholm': ['Dubrovnik', 'Lisbon', 'Copenhagen', 'Prague', 'Split', 'Tallinn'],
        'Split': ['Stockholm', 'Lyon', 'Prague', 'Copenhagen'],
        'Lyon': ['Split', 'Prague', 'Lisbon'],
    }

    constraints = {
        'Lisbon': lambda start, end: 4 in range(start, end + 1) or 5 in range(start, end + 1),
        'Stockholm': lambda start, end: any(d in range(start, end + 1) for d in range(13, 17)),
        'Lyon': lambda start, end: any(d in range(start, end + 1) for d in range(18, 20)),
        'Tallinn': lambda start, end: any(d in range(start, end + 1) for d in range(1, 3)),
    }

    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i + 1]
            if next_city not in direct_flights[current]:
                valid = False
                break
        if not valid:
            continue

        start_days = {}
        end_days = {}
        current_start = 1
        for city in perm:
            duration = durations[city]
            end_day = current_start + duration - 1
            start_days[city] = current_start
            end_days[city] = end_day
            current_start = end_day  # Next city starts on the same day as the previous end day

        # Check constraints
        for city, check in constraints.items():
            s = start_days[city]
            e = end_days[city]
            if not check(s, e):
                valid = False
                break
        if not valid:
            continue

        # Generate itinerary
        itinerary = []
        for city in perm:
            s = start_days[city]
            e = end_days[city]
            day_range = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range, "place": city})

        print(json.dumps({"itinerary": itinerary}, indent=2))
        return

    print("No valid itinerary found.")

if __name__ == "__main__":
    main()