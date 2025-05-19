import json
import itertools

# Input parameters
cities = {
    'Vienna': 4,
    'Barcelona': 2,
    'Edinburgh': 4,
    'Krakow': 3,
    'Riga': 4,
    'Hamburg': 2,
    'Paris': 2,
    'Stockholm': 2
}

constraints = {
    'Vienna': ['Hamburg', 'Barcelona'],
    'Barcelona': ['Krakow', 'Stockholm', 'Riga', 'Hamburg'],
    'Edinburgh': ['Stockholm', 'Krakow', 'Riga'],
    'Krakow': ['Barcelona', 'Stockholm', 'Edinburgh', 'Paris'],
    'Riga': ['Barcelona', 'Stockholm', 'Edinburgh', 'Paris'],
    'Hamburg': ['Vienna', 'Stockholm', 'Barcelona', 'Paris'],
    'Paris': ['Edinburgh', 'Krakow', 'Riga', 'Stockholm', 'Vienna'],
    'Stockholm': ['Hamburg', 'Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Paris']
}

# Direct flights
flights = {
    ('Hamburg', 'Stockholm'): 1,
    ('Vienna', 'Stockholm'): 1,
    ('Paris', 'Edinburgh'): 1,
    ('Riga', 'Barcelona'): 1,
    ('Paris', 'Riga'): 1,
    ('Krakow', 'Barcelona'): 1,
    ('Edinburgh', 'Stockholm'): 1,
    ('Paris', 'Krakow'): 1,
    ('Krakow', 'Stockholm'): 1,
    ('Riga', 'Edinburgh'): 1,
    ('Barcelona', 'Stockholm'): 1,
    ('Paris', 'Stockholm'): 1,
    ('Krakow', 'Edinburgh'): 1,
    ('Vienna', 'Hamburg'): 1,
    ('Paris', 'Hamburg'): 1,
    ('Riga', 'Stockholm'): 1,
    ('Hamburg', 'Barcelona'): 1,
    ('Vienna', 'Barcelona'): 1,
    ('Krakow', 'Vienna'): 1,
    ('Riga', 'Hamburg'): 1,
    ('Barcelona', 'Edinburgh'): 1,
    ('Paris', 'Barcelona'): 1,
    ('Hamburg', 'Edinburgh'): 1,
    ('Paris', 'Vienna'): 1,
    ('Vienna', 'Riga'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 16)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))