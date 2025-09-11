import json

def main():
    # Define direct flights as a set of frozensets for easy lookup
    direct_flights = {
        frozenset(['Amsterdam', 'Warsaw']),
        frozenset(['Helsinki', 'Brussels']),
        frozenset(['Helsinki', 'Warsaw']),
        frozenset(['Reykjavik', 'Brussels']),
        frozenset(['Amsterdam', 'Lyon']),
        frozenset(['Amsterdam', 'Naples']),
        frozenset(['Amsterdam', 'Reykjavik']),
        frozenset(['Naples', 'Valencia']),
        frozenset(['Porto', 'Brussels']),
        frozenset(['Amsterdam', 'Split']),
        frozenset(['Lyon', 'Split']),
        frozenset(['Warsaw', 'Split']),
        frozenset(['Porto', 'Amsterdam']),
        frozenset(['Helsinki', 'Split']),
        frozenset(['Brussels', 'Lyon']),
        frozenset(['Porto', 'Lyon']),
        frozenset(['Reykjavik', 'Warsaw']),
        frozenset(['Brussels', 'Valencia']),
        frozenset(['Valencia', 'Lyon']),
        frozenset(['Porto', 'Valencia']),
        frozenset(['Warsaw', 'Valencia']),
        frozenset(['Amsterdam', 'Helsinki']),
        frozenset(['Porto', 'Valencia']),
        frozenset(['Warsaw', 'Brussels']),
        frozenset(['Warsaw', 'Naples']),
        frozenset(['Naples', 'Split']),
        frozenset(['Helsinki', 'Naples']),
        frozenset(['Helsinki', 'Reykjavik']),
        frozenset(['Amsterdam', 'Valencia']),
    }

    # Define cities in the correct order with start_day and duration
    cities_order = [
        {'name': 'Porto', 'start_day': 1, 'duration': 5},
        {'name': 'Amsterdam', 'start_day': 5, 'duration': 4},
        {'name': 'Helsinki', 'start_day': 8, 'duration': 4},
        {'name': 'Reykjavik', 'start_day': 11, 'duration': 5},
        {'name': 'Warsaw', 'start_day': 15, 'duration': 3},
        {'name': 'Naples', 'start_day': 17, 'duration': 4},
        {'name': 'Brussels', 'start_day': 20, 'duration': 3},
        {'name': 'Valencia', 'start_day': 22, 'duration': 2},
        {'name': 'Lyon', 'start_day': 23, 'duration': 3},
        {'name': 'Split', 'start_day': 25, 'duration': 3},
    ]

    # Verify direct flights between consecutive cities
    for i in range(len(cities_order) - 1):
        city_a = cities_order[i]['name']
        city_b = cities_order[i + 1]['name']
        if frozenset([city_a, city_b]) not in direct_flights:
            raise ValueError(f"No direct flight between {city_a} and {city_b}")

    # Generate the itinerary
    itinerary = []
    for city in cities_order:
        start_day = city['start_day']
        duration = city['duration']
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city['name']})

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()