import itertools
import json

def main():
    cities = {
        'Oslo': {'duration': 2},
        'Reykjavik': {'duration': 5},
        'Stockholm': {'duration': 4},
        'Munich': {'duration': 4},
        'Frankfurt': {'duration': 4},
        'Barcelona': {'duration': 3},
        'Bucharest': {'duration': 2},
        'Split': {'duration': 3},
    }

    # Time constraints for each city
    time_constraints = {
        'Oslo': lambda start, end: start == 16 and end == 17,
        'Reykjavik': lambda start, end: any(9 <= day <= 13 for day in range(start, end + 1)),
        'Stockholm': lambda start, end: True,
        'Munich': lambda start, end: any(13 <= day <= 16 for day in range(start, end + 1)),
        'Frankfurt': lambda start, end: start == 17 and end == 20,
        'Barcelona': lambda start, end: True,
        'Bucharest': lambda start, end: True,
        'Split': lambda start, end: True,
    }

    # Direct flights (bidirectional)
    direct_flights = {
        ('Reykjavik', 'Munich'),
        ('Munich', 'Frankfurt'),
        ('Split', 'Oslo'),
        ('Reykjavik', 'Oslo'),
        ('Bucharest', 'Munich'),
        ('Oslo', 'Frankfurt'),
        ('Bucharest', 'Barcelona'),
        ('Barcelona', 'Frankfurt'),
        ('Reykjavik', 'Frankfurt'),
        ('Barcelona', 'Stockholm'),
        ('Barcelona', 'Reykjavik'),
        ('Stockholm', 'Reykjavik'),
        ('Barcelona', 'Split'),
        ('Bucharest', 'Oslo'),
        ('Bucharest', 'Frankfurt'),
        ('Split', 'Frankfurt'),
        ('Barcelona', 'Oslo'),
        ('Stockholm', 'Munich'),
        ('Stockholm', 'Oslo'),
        ('Split', 'Stockholm'),
        ('Barcelona', 'Munich'),
        ('Stockholm', 'Frankfurt'),
        ('Munich', 'Oslo'),
        ('Split', 'Munich'),
    }

    # Add reverse flights
    for a, b in list(direct_flights):
        direct_flights.add((b, a))

    # Generate all permutations of cities
    for perm in itertools.permutations(cities.keys()):
        # Check if consecutive cities have direct flights
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i + 1]
            if (current, next_city) not in direct_flights:
                valid = False
                break
        if not valid:
            continue

        # Calculate start and end days for each city
        start_day = 1
        city_days = []
        for city in perm:
            duration = cities[city]['duration']
            end_day = start_day + duration - 1
            city_days.append((city, start_day, end_day))
            start_day = end_day  # next city starts on this day

        # Now check time constraints
        all_constraints_satisfied = True
        for city, start, end in city_days:
            if not time_constraints[city](start, end):
                all_constraints_satisfied = False
                break
        if all_constraints_satisfied:
            # Build the itinerary
            itinerary = []
            for city, start, end in city_days:
                day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
            print(json.dumps({"itinerary": itinerary}))
            return

    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()