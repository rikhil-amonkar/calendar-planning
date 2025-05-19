import json
import itertools

# Input parameters
cities = {
    'Paris': 6,
    'Oslo': 5,
    'Porto': 7,
    'Geneva': 7,
    'Reykjavik': 2
}

constraints = {
    'Paris': ['Oslo'],
    'Oslo': ['Geneva'],
    'Porto': ['Paris'],
    'Geneva': ['Paris', 'Porto'],
    'Reykjavik': []
}

# Direct flights
flights = {
    ('Paris', 'Oslo'): 1,
    ('Geneva', 'Oslo'): 1,
    ('Porto', 'Paris'): 1,
    ('Geneva', 'Paris'): 1,
    ('Geneva', 'Porto'): 1,
    ('Paris', 'Reykjavik'): 1,
    ('Reykjavik', 'Oslo'): 1,
    ('Porto', 'Oslo'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 23)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))