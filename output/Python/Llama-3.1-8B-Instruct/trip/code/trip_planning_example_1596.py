import json
import itertools

# Input parameters
cities = {
    'Bucharest': 2,
    'Krakow': 4,
    'Munich': 3,
    'Barcelona': 5,
    'Warsaw': 5,
    'Budapest': 5,
    'Stockholm': 2,
    'Riga': 5,
    'Edinburgh': 5,
    'Vienna': 5
}

constraints = {
    'Bucharest': ['Riga'],
    'Krakow': ['Munich', 'Warsaw', 'Budapest'],
    'Munich': ['Krakow', 'Warsaw', 'Bucharest', 'Budapest'],
    'Barcelona': ['Warsaw', 'Budapest', 'Stockholm', 'Riga', 'Vienna'],
    'Warsaw': ['Budapest', 'Barcelona', 'Krakow', 'Vienna', 'Munich', 'Riga', 'Edinburgh'],
    'Budapest': ['Vienna', 'Warsaw', 'Barcelona', 'Riga', 'Munich', 'Edinburgh'],
    'Stockholm': ['Krakow', 'Barcelona', 'Munich', 'Vienna', 'Riga', 'Warsaw', 'Budapest', 'Edinburgh'],
    'Riga': ['Munich', 'Budapest', 'Barcelona', 'Warsaw', 'Vienna', 'Stockholm', 'Bucharest'],
    'Edinburgh': ['Warsaw', 'Budapest', 'Barcelona', 'Munich', 'Vienna', 'Riga', 'Stockholm', 'Krakow'],
    'Vienna': ['Bucharest', 'Riga', 'Warsaw', 'Krakow', 'Budapest', 'Barcelona', 'Munich', 'Stockholm', 'Edinburgh']
}

# Direct flights
flights = {
    ('Budapest', 'Munich'): 1,
    ('Bucharest', 'Riga'): 1,
    ('Munich', 'Krakow'): 1,
    ('Munich', 'Warsaw'): 1,
    ('Munich', 'Bucharest'): 1,
    ('Edinburgh', 'Stockholm'): 1,
    ('Barcelona', 'Warsaw'): 1,
    ('Edinburgh', 'Krakow'): 1,
    ('Barcelona', 'Munich'): 1,
    ('Stockholm', 'Krakow'): 1,
    ('Budapest', 'Vienna'): 1,
    ('Barcelona', 'Stockholm'): 1,
    ('Stockholm', 'Munich'): 1,
    ('Edinburgh', 'Budapest'): 1,
    ('Barcelona', 'Riga'): 1,
    ('Edinburgh', 'Barcelona'): 1,
    ('Vienna', 'Riga'): 1,
    ('Barcelona', 'Vienna'): 1,
    ('Bucharest', 'Warsaw'): 1,
    ('Vienna', 'Krakow'): 1,
    ('Edinburgh', 'Munich'): 1,
    ('Barcelona', 'Bucharest'): 1,
    ('Edinburgh', 'Riga'): 1,
    ('Vienna', 'Stockholm'): 1,
    ('Warsaw', 'Krakow'): 1,
    ('Barcelona', 'Krakow'): 1,
    ('Riga', 'Munich'): 1,
    ('Vienna', 'Bucharest'): 1,
    ('Budapest', 'Warsaw'): 1,
    ('Vienna', 'Warsaw'): 1,
    ('Barcelona', 'Vienna'): 1,
    ('Budapest', 'Bucharest'): 1,
    ('Vienna', 'Munich'): 1,
    ('Riga', 'Warsaw'): 1,
    ('Stockholm', 'Riga'): 1,
    ('Stockholm', 'Warsaw'): 1
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