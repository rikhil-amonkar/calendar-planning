import json
import itertools

# Input parameters
cities = {
    'Venice': 4,
    'Barcelona': 3,
    'Copenhagen': 4,
    'Lyon': 4,
    'Reykjavik': 4,
    'Dubrovnik': 5,
    'Athens': 2,
    'Tallinn': 5,
    'Munich': 3
}

constraints = {
    'Venice': ['Munich'],
    'Barcelona': ['Reykjavik'],
    'Copenhagen': ['Athens', 'Dubrovnik', 'Reykjavik'],
    'Lyon': ['Barcelona', 'Munich'],
    'Reykjavik': ['Munich', 'Athens'],
    'Dubrovnik': ['Munich', 'Athens'],
    'Athens': ['Munich', 'Dubrovnik'],
    'Tallinn': ['Barcelona', 'Copenhagen', 'Munich'],
    'Munich': ['Venice', 'Barcelona', 'Tallinn', 'Dubrovnik', 'Athens', 'Lyon', 'Copenhagen']
}

# Direct flights
flights = {
    ('Copenhagen', 'Athens'): 1,
    ('Copenhagen', 'Dubrovnik'): 1,
    ('Munich', 'Tallinn'): 1,
    ('Copenhagen', 'Munich'): 1,
    ('Venice', 'Munich'): 1,
    ('Reykjavik', 'Athens'): 1,
    ('Athens', 'Dubrovnik'): 1,
    ('Venice', 'Athens'): 1,
    ('Lyon', 'Barcelona'): 1,
    ('Copenhagen', 'Reykjavik'): 1,
    ('Reykjavik', 'Munich'): 1,
    ('Athens', 'Munich'): 1,
    ('Lyon', 'Munich'): 1,
    ('Barcelona', 'Reykjavik'): 1,
    ('Venice', 'Copenhagen'): 1,
    ('Barcelona', 'Dubrovnik'): 1,
    ('Lyon', 'Venice'): 1,
    ('Dubrovnik', 'Munich'): 1,
    ('Barcelona', 'Athens'): 1,
    ('Copenhagen', 'Barcelona'): 1,
    ('Venice', 'Barcelona'): 1,
    ('Barcelona', 'Munich'): 1,
    ('Barcelona', 'Tallinn'): 1,
    ('Copenhagen', 'Tallinn'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 26)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))