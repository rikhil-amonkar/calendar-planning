import json
import itertools

# Input parameters
cities = {
    'Istanbul': 4,
    'Vienna': 4,
    'Riga': 2,
    'Brussels': 2,
    'Madrid': 4,
    'Vilnius': 4,
    'Venice': 5,
    'Geneva': 4,
    'Munich': 5,
    'Reykjavik': 2
}

constraints = {
    'Istanbul': ['Brussels', 'Vienna', 'Vilnius'],
    'Vienna': ['Vilnius', 'Riga', 'Istanbul', 'Geneva', 'Munich'],
    'Riga': ['Brussels', 'Istanbul'],
    'Brussels': ['Istanbul', 'Riga', 'Geneva', 'Madrid', 'Vilnius', 'Munich', 'Vienna'],
    'Madrid': ['Munich', 'Venice', 'Istanbul', 'Geneva', 'Brussels'],
    'Vilnius': ['Istanbul', 'Brussels', 'Vienna', 'Munich', 'Geneva'],
    'Venice': ['Brussels', 'Munich', 'Madrid', 'Istanbul', 'Vienna'],
    'Geneva': ['Istanbul', 'Vienna', 'Brussels', 'Madrid', 'Munich'],
    'Munich': ['Reykjavik', 'Istanbul', 'Brussels', 'Vienna', 'Geneva', 'Vilnius', 'Madrid'],
    'Reykjavik': ['Vienna', 'Brussels']
}

# Direct flights
flights = {
    ('Munich', 'Vienna'): 1,
    ('Istanbul', 'Brussels'): 1,
    ('Vienna', 'Vilnius'): 1,
    ('Madrid', 'Munich'): 1,
    ('Venice', 'Brussels'): 1,
    ('Riga', 'Brussels'): 1,
    ('Geneva', 'Istanbul'): 1,
    ('Munich', 'Reykjavik'): 1,
    ('Vienna', 'Istanbul'): 1,
    ('Riga', 'Istanbul'): 1,
    ('Reykjavik', 'Vienna'): 1,
    ('Venice', 'Munich'): 1,
    ('Madrid', 'Venice'): 1,
    ('Vilnius', 'Istanbul'): 1,
    ('Venice', 'Vienna'): 1,
    ('Venice', 'Istanbul'): 1,
    ('Reykjavik', 'Madrid'): 1,
    ('Riga', 'Munich'): 1,
    ('Munich', 'Istanbul'): 1,
    ('Reykjavik', 'Brussels'): 1,
    ('Vilnius', 'Brussels'): 1,
    ('Vilnius', 'Munich'): 1,
    ('Madrid', 'Vienna'): 1,
    ('Vienna', 'Riga'): 1,
    ('Geneva', 'Vienna'): 1,
    ('Madrid', 'Brussels'): 1,
    ('Vienna', 'Brussels'): 1,
    ('Geneva', 'Brussels'): 1,
    ('Geneva', 'Madrid'): 1,
    ('Munich', 'Brussels'): 1,
    ('Madrid', 'Istanbul'): 1,
    ('Geneva', 'Munich'): 1,
    ('Riga', 'Vilnius'): 1
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