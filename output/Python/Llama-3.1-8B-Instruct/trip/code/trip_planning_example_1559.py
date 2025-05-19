import json
import itertools

# Input parameters
cities = {
    'Valencia': 2,
    'Oslo': 3,
    'Lyon': 4,
    'Prague': 3,
    'Paris': 4,
    'Nice': 4,
    'Seville': 5,
    'Tallinn': 2,
    'Mykonos': 5,
    'Lisbon': 2
}

constraints = {
    'Valencia': ['Paris', 'Lisbon'],
    'Oslo': ['Nice', 'Paris'],
    'Lyon': ['Nice', 'Paris', 'Prague', 'Valencia'],
    'Prague': ['Lyon', 'Paris', 'Oslo', 'Lisbon', 'Valencia'],
    'Paris': ['Oslo', 'Lyon', 'Nice', 'Seville', 'Tallinn', 'Prague', 'Valencia', 'Lisbon'],
    'Nice': ['Oslo', 'Paris', 'Lyon', 'Mykonos', 'Lisbon'],
    'Seville': ['Paris', 'Lisbon'],
    'Tallinn': ['Paris', 'Oslo'],
    'Mykonos': ['Nice'],
    'Lisbon': ['Seville', 'Paris', 'Nice', 'Oslo', 'Valencia']
}

# Direct flights
flights = {
    ('Lisbon', 'Paris'): 1,
    ('Lyon', 'Nice'): 1,
    ('Tallinn', 'Oslo'): 1,
    ('Prague', 'Lyon'): 1,
    ('Paris', 'Oslo'): 1,
    ('Lisbon', 'Seville'): 1,
    ('Prague', 'Lisbon'): 1,
    ('Oslo', 'Nice'): 1,
    ('Valencia', 'Paris'): 1,
    ('Valencia', 'Lisbon'): 1,
    ('Paris', 'Nice'): 1,
    ('Nice', 'Mykonos'): 1,
    ('Paris', 'Lyon'): 1,
    ('Valencia', 'Lyon'): 1,
    ('Prague', 'Oslo'): 1,
    ('Prague', 'Paris'): 1,
    ('Seville', 'Paris'): 1,
    ('Oslo', 'Lyon'): 1,
    ('Prague', 'Valencia'): 1,
    ('Lisbon', 'Nice'): 1,
    ('Lisbon', 'Oslo'): 1,
    ('Valencia', 'Seville'): 1,
    ('Lisbon', 'Lyon'): 1,
    ('Paris', 'Tallinn'): 1,
    ('Prague', 'Tallinn'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 25)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))