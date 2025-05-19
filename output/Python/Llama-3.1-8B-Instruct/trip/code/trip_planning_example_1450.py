import json
import itertools

# Input parameters
cities = {
    'Stockholm': 3,
    'Hamburg': 5,
    'Florence': 2,
    'Istanbul': 5,
    'Oslo': 5,
    'Vilnius': 5,
    'Santorini': 2,
    'Munich': 5,
    'Frankfurt': 4,
    'Krakow': 5
}

constraints = {
    'Stockholm': ['Hamburg', 'Munich', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Frankfurt', 'Krakow'],
    'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Frankfurt'],
    'Florence': ['Frankfurt', 'Munich'],
    'Istanbul': ['Stockholm', 'Hamburg', 'Oslo', 'Vilnius', 'Munich', 'Frankfurt'],
    'Oslo': ['Stockholm', 'Istanbul', 'Vilnius', 'Munich', 'Hamburg', 'Frankfurt', 'Santorini'],
    'Vilnius': ['Oslo', 'Istanbul', 'Munich', 'Hamburg', 'Frankfurt'],
    'Santorini': ['Oslo', 'Munich'],
    'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Frankfurt', 'Krakow'],
    'Frankfurt': ['Istanbul', 'Oslo', 'Vilnius', 'Munich', 'Hamburg', 'Florence', 'Stockholm', 'Krakow'],
    'Krakow': ['Frankfurt', 'Munich', 'Istanbul', 'Oslo', 'Vilnius', 'Hamburg', 'Stockholm']
}

# Direct flights
flights = {
    ('Oslo', 'Stockholm'): 1,
    ('Krakow', 'Frankfurt'): 1,
    ('Krakow', 'Istanbul'): 1,
    ('Munich', 'Stockholm'): 1,
    ('Hamburg', 'Stockholm'): 1,
    ('Krakow', 'Vilnius'): 1,
    ('Oslo', 'Istanbul'): 1,
    ('Istanbul', 'Stockholm'): 1,
    ('Oslo', 'Krakow'): 1,
    ('Vilnius', 'Istanbul'): 1,
    ('Oslo', 'Vilnius'): 1,
    ('Frankfurt', 'Istanbul'): 1,
    ('Oslo', 'Frankfurt'): 1,
    ('Munich', 'Hamburg'): 1,
    ('Munich', 'Istanbul'): 1,
    ('Oslo', 'Munich'): 1,
    ('Frankfurt', 'Florence'): 1,
    ('Oslo', 'Hamburg'): 1,
    ('Vilnius', 'Frankfurt'): 1,
    ('Florence', 'Munich'): 1,
    ('Krakow', 'Munich'): 1,
    ('Hamburg', 'Istanbul'): 1,
    ('Frankfurt', 'Stockholm'): 1,
    ('Stockholm', 'Santorini'): 1,
    ('Frankfurt', 'Munich'): 1,
    ('Santorini', 'Oslo'): 1,
    ('Krakow', 'Stockholm'): 1,
    ('Vilnius', 'Munich'): 1,
    ('Frankfurt', 'Hamburg'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 32)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))