import json

def main():
    cities = {
        'Istanbul': 5,
        'Brussels': 3,
        'Milan': 4,
        'Split': 4,
        'Helsinki': 3,
        'Dubrovnik': 2,
        'Frankfurt': 3,
        'Vilnius': 5,
    }

    fixed_constraints = {
        'Istanbul': (1, 5),
        'Frankfurt': (16, 18),
        'Vilnius': (18, 22),
    }

    order = ['Istanbul', 'Brussels', 'Milan', 'Split', 'Helsinki', 'Dubrovnik', 'Frankfurt', 'Vilnius']

    direct_flights = {
        frozenset(('Milan', 'Frankfurt')),
        frozenset(('Split', 'Frankfurt')),
        frozenset(('Milan', 'Split')),
        frozenset(('Brussels', 'Vilnius')),
        frozenset(('Brussels', 'Helsinki')),
        frozenset(('Istanbul', 'Brussels')),
        frozenset(('Milan', 'Vilnius')),
        frozenset(('Brussels', 'Milan')),
        frozenset(('Istanbul', 'Helsinki')),
        frozenset(('Helsinki', 'Vilnius')),
        frozenset(('Helsinki', 'Dubrovnik')),
        frozenset(('Split', 'Vilnius')),
        frozenset(('Dubrovnik', 'Istanbul')),
        frozenset(('Istanbul', 'Milan')),
        frozenset(('Helsinki', 'Frankfurt')),
        frozenset(('Istanbul', 'Vilnius')),
        frozenset(('Split', 'Helsinki')),
        frozenset(('Milan', 'Helsinki')),
        frozenset(('Istanbul', 'Frankfurt')),
        frozenset(('Brussels', 'Frankfurt')),
        frozenset(('Dubrovnik', 'Frankfurt')),
        frozenset(('Frankfurt', 'Vilnius')),
    }

    itinerary = []
    previous_end = 0

    for city in order:
        duration = cities[city]
        if city in fixed_constraints:
            start_day, end_day = fixed_constraints[city]
            if previous_end > start_day:
                raise ValueError(f"Conflict in order for city {city}")
            previous_end = end_day
        else:
            start_day = previous_end
            end_day = start_day + duration - 1
            previous_end = end_day
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})

    # Check transitions
    for i in range(len(order) - 1):
        current_city = order[i]
        next_city = order[i+1]
        if frozenset((current_city, next_city)) not in direct_flights:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()