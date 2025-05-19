import json
import itertools

# Input parameters
cities = {
    'Tallinn': 2,
    'Bucharest': 4,
    'Seville': 5,
    'Stockholm': 5,
    'Munich': 5,
    'Milan': 2
}

constraints = {
    'Tallinn': ['Stockholm'],
    'Bucharest': ['Munich'],
    'Seville': ['Munich', 'Milan'],
    'Stockholm': ['Tallinn', 'Munich', 'Milan'],
    'Munich': ['Bucharest', 'Seville', 'Stockholm', 'Milan', 'Tallinn'],
    'Milan': ['Stockholm', 'Munich']
}

# Direct flights
flights = {
    ('Milan', 'Stockholm'): 1,
    ('Munich', 'Stockholm'): 1,
    ('Bucharest', 'Munich'): 1,
    ('Munich', 'Seville'): 1,
    ('Stockholm', 'Tallinn'): 1,
    ('Munich', 'Milan'): 1,
    ('Munich', 'Tallinn'): 1,
    ('Seville', 'Milan'): 1
}

def compute_itinerary(cities, constraints, flights, total_days):
    # Initialize the itinerary
    itinerary = []
    current_city = None
    current_day = 1

    # Visit each city
    for city, duration in cities.items():
        # Find the next city to visit
        next_cities = constraints[city]
        if current_city is not None:
            next_cities = [c for c in next_cities if flights.get((current_city, c), 0) > 0]

        # Find the first available city to visit
        next_city = None
        for c in next_cities:
            if current_day + duration <= total_days and flights.get((current_city, c), 0) > 0:
                next_city = c
                break

        # Add the current city to the itinerary
        if current_city is not None:
            itinerary.append({'day_range': f'Day {current_day}-{current_day + duration - 1}', 'place': current_city})

        # Add the flight to the next city
        if next_city is not None:
            itinerary.append({'flying': f'Day {current_day + duration - 1}-{current_day + duration - 1}', 'from': current_city, 'to': next_city})

        # Update the current city and day
        current_city = next_city
        current_day += duration

    # Add the last city to the itinerary
    if current_city is not None:
        itinerary.append({'day_range': f'Day {current_day - cities[current_city]}-{current_day - 1}', 'place': current_city})

    return itinerary

# Compute the itinerary
itinerary = compute_itinerary(cities, constraints, flights, 18)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))