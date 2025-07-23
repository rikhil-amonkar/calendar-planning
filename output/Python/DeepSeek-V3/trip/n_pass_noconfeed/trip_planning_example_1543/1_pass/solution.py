import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Prague': {'duration': 3, 'constraints': [('workshop', 1, 3)]},
        'Warsaw': {'duration': 4, 'constraints': [('meet friends', 20, 23)]},
        'Dublin': {'duration': 3, 'constraints': []},
        'Athens': {'duration': 3, 'constraints': []},
        'Vilnius': {'duration': 4, 'constraints': []},
        'Porto': {'duration': 5, 'constraints': [('conference', 16, 20)]},
        'London': {'duration': 3, 'constraints': [('wedding', 3, 5)]},
        'Seville': {'duration': 2, 'constraints': []},
        'Lisbon': {'duration': 5, 'constraints': [('visit relatives', 5, 9)]},
        'Dubrovnik': {'duration': 3, 'constraints': []}
    }

    direct_flights = {
        'Warsaw': ['Vilnius', 'London', 'Athens', 'Lisbon', 'Porto', 'Prague', 'Dublin'],
        'Vilnius': ['Warsaw', 'Athens'],
        'Prague': ['Athens', 'Lisbon', 'London', 'Warsaw', 'Dublin'],
        'Athens': ['Prague', 'Vilnius', 'Dublin', 'Warsaw', 'Dubrovnik', 'London', 'Lisbon'],
        'London': ['Lisbon', 'Dublin', 'Prague', 'Warsaw', 'Athens'],
        'Lisbon': ['London', 'Porto', 'Prague', 'Athens', 'Warsaw', 'Dublin', 'Seville'],
        'Porto': ['Lisbon', 'Seville', 'Warsaw', 'Dublin'],
        'Dublin': ['London', 'Seville', 'Athens', 'Prague', 'Dubrovnik', 'Porto', 'Lisbon'],
        'Seville': ['Dublin', 'Porto', 'Lisbon'],
        'Dubrovnik': ['Athens', 'Dublin']
    }

    # Fixed constraints
    fixed_assignments = {
        'Prague': (1, 3),
        'London': (3, 5),
        'Lisbon': (5, 9),
        'Porto': (16, 20),
        'Warsaw': (20, 23)
    }

    # Assign fixed cities first
    itinerary = {}
    for city, (start, end) in fixed_assignments.items():
        for day in range(start, end + 1):
            itinerary[day] = city
        cities[city]['duration'] -= (end - start + 1)

    # Remaining cities and their durations
    remaining_cities = [city for city in cities if cities[city]['duration'] > 0]
    remaining_durations = {city: cities[city]['duration'] for city in remaining_cities}

    # Find available days (days not in itinerary)
    all_days = set(range(1, 27))
    used_days = set(itinerary.keys())
    available_days = sorted(list(all_days - used_days))

    # Assign remaining cities to available days
    current_day = min(available_days)
    current_city = None
    for day in available_days:
        if day in itinerary:
            continue
        if current_city is None or remaining_durations[current_city] == 0:
            for city in remaining_cities:
                if remaining_durations[city] > 0:
                    # Check if we can reach this city from the previous city
                    prev_city = itinerary.get(day - 1, None)
                    if prev_city is None or city in direct_flights[prev_city] or prev_city == city:
                        current_city = city
                        break
            if current_city is None:
                continue
        itinerary[day] = current_city
        remaining_durations[current_city] -= 1
        if remaining_durations[current_city] == 0:
            current_city = None

    # Group consecutive days
    grouped_itinerary = []
    current_place = None
    start_day = None
    for day in range(1, 27):
        place = itinerary.get(day, None)
        if place != current_place:
            if current_place is not None:
                grouped_itinerary.append({
                    'day_range': f'Day {start_day}-{day - 1}',
                    'place': current_place
                })
            current_place = place
            start_day = day
    if current_place is not None:
        grouped_itinerary.append({
            'day_range': f'Day {start_day}-26',
            'place': current_place
        })

    return {'itinerary': grouped_itinerary}

result = find_itinerary()
print(json.dumps(result, indent=2))