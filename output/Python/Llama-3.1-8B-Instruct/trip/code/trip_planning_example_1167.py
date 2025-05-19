import json
import itertools

# Input parameters
cities = {
    'Dublin': 5,
    'Krakow': 4,
    'Istanbul': 3,
    'Venice': 3,
    'Naples': 4,
    'Brussels': 2,
    'Mykonos': 4,
    'Frankfurt': 3
}

constraints = {
    'Dublin': ['Brussels', 'Krakow', 'Naples', 'Istanbul', 'Venice'],
    'Krakow': ['Dublin', 'Brussels', 'Istanbul', 'Frankfurt'],
    'Istanbul': ['Naples', 'Brussels', 'Frankfurt', 'Dublin', 'Venice'],
    'Venice': ['Istanbul', 'Brussels', 'Naples', 'Frankfurt', 'Dublin'],
    'Naples': ['Dublin', 'Istanbul', 'Brussels', 'Venice', 'Frankfurt'],
    'Brussels': ['Venice', 'Frankfurt', 'Naples', 'Krakow', 'Dublin'],
    'Mykonos': ['Naples'],
    'Frankfurt': ['Krakow', 'Brussels', 'Naples', 'Venice', 'Dublin']
}

# Direct flights
flights = {
    ('Dublin', 'Brussels'): 1,
    ('Mykonos', 'Naples'): 1,
    ('Venice', 'Istanbul'): 1,
    ('Frankfurt', 'Krakow'): 1,
    ('Naples', 'Dublin'): 1,
    ('Krakow', 'Brussels'): 1,
    ('Naples', 'Istanbul'): 1,
    ('Naples', 'Brussels'): 1,
    ('Istanbul', 'Frankfurt'): 1,
    ('Brussels', 'Frankfurt'): 1,
    ('Istanbul', 'Krakow'): 1,
    ('Istanbul', 'Brussels'): 1,
    ('Venice', 'Frankfurt'): 1,
    ('Naples', 'Frankfurt'): 1,
    ('Dublin', 'Krakow'): 1,
    ('Venice', 'Brussels'): 1,
    ('Naples', 'Venice'): 1,
    ('Istanbul', 'Dublin'): 1,
    ('Venice', 'Dublin'): 1,
    ('Dublin', 'Frankfurt'): 1
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
itinerary = compute_itinerary(cities, constraints, flights, 21)

# Print the itinerary as JSON
print(json.dumps(itinerary, indent=4))