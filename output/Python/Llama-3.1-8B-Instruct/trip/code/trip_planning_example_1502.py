import json
import itertools

# Input parameters
cities = {
    'Santorini': 3,
    'Valencia': 4,
    'Madrid': 2,
    'Seville': 2,
    'Bucharest': 3,
    'Vienna': 4,
    'Riga': 4,
    'Tallinn': 5,
    'Krakow': 5,
    'Frankfurt': 4
}

constraints = {
    'Santorini': ['Madrid'],
    'Valencia': ['Madrid', 'Seville'],
    'Madrid': ['Santorini', 'Valencia', 'Seville', 'Bucharest'],
    'Seville': ['Valencia', 'Madrid'],
    'Bucharest': ['Vienna', 'Riga', 'Valencia'],
    'Vienna': ['Bucharest', 'Seville', 'Riga', 'Krakow', 'Frankfurt'],
    'Riga': ['Bucharest', 'Vienna', 'Tallinn'],
    'Tallinn': ['Riga'],
    'Krakow': ['Valencia', 'Frankfurt'],
    'Frankfurt': ['Krakow', 'Tallinn', 'Bucharest']
}

# Direct flights
flights = {
    ('Santorini', 'Madrid'): 1,
    ('Santorini', 'Bucharest'): 1,
    ('Madrid', 'Santorini'): 1,
    ('Madrid', 'Valencia'): 1,
    ('Madrid', 'Seville'): 1,
    ('Madrid', 'Bucharest'): 1,
    ('Seville', 'Valencia'): 1,
    ('Seville', 'Madrid'): 1,
    ('Valencia', 'Bucharest'): 1,
    ('Valencia', 'Madrid'): 1,
    ('Valencia', 'Seville'): 1,
    ('Valencia', 'Krakow'): 1,
    ('Valencia', 'Frankfurt'): 1,
    ('Bucharest', 'Vienna'): 1,
    ('Bucharest', 'Riga'): 1,
    ('Bucharest', 'Valencia'): 1,
    ('Bucharest', 'Frankfurt'): 1,
    ('Bucharest', 'Madrid'): 1,
    ('Vienna', 'Bucharest'): 1,
    ('Vienna', 'Seville'): 1,
    ('Vienna', 'Riga'): 1,
    ('Vienna', 'Krakow'): 1,
    ('Vienna', 'Frankfurt'): 1,
    ('Vienna', 'Madrid'): 1,
    ('Riga', 'Bucharest'): 1,
    ('Riga', 'Vienna'): 1,
    ('Riga', 'Tallinn'): 1,
    ('Tallinn', 'Riga'): 1,
    ('Tallinn', 'Frankfurt'): 1,
    ('Tallinn', 'Bucharest'): 1,
    ('Krakow', 'Valencia'): 1,
    ('Krakow', 'Frankfurt'): 1,
    ('Krakow', 'Vienna'): 1,
    ('Frankfurt', 'Tallinn'): 1,
    ('Frankfurt', 'Bucharest'): 1,
    ('Frankfurt', 'Krakow'): 1,
    ('Frankfurt', 'Riga'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 27)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))