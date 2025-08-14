import json

# Define cities and their durations
cities_durations = {
    'Paris': 5,
    'Warsaw': 2,
    'Krakow': 2,
    'Tallinn': 2,
    'Riga': 2,
    'Copenhagen': 5,
    'Helsinki': 5,
    'Oslo': 5,
    'Santorini': 2,
    'Lyon': 4
}

# Define direct flight connections (bidirectional)
flights = {
    'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Helsinki', 'Krakow', 'Oslo', 'Paris'],
    'Riga': ['Warsaw', 'Tallinn', 'Copenhagen', 'Helsinki', 'Oslo', 'Paris'],
    'Copenhagen': ['Helsinki', 'Oslo', 'Paris', 'Warsaw', 'Riga', 'Krakow'],
    'Lyon': ['Paris', 'Oslo'],
    'Paris': ['Warsaw', 'Tallinn', 'Oslo', 'Riga', 'Krakow', 'Copenhagen', 'Helsinki', 'Lyon'],
    'Oslo': ['Lyon', 'Paris', 'Copenhagen', 'Riga', 'Tallinn', 'Helsinki', 'Krakow'],
    'Krakow': ['Warsaw', 'Helsinki', 'Copenhagen', 'Oslo'],
    'Helsinki': ['Copenhagen', 'Oslo', 'Tallinn', 'Riga', 'Krakow', 'Paris'],
    'Tallinn': ['Warsaw', 'Riga', 'Helsinki', 'Oslo', 'Paris'],
    'Santorini': ['Oslo']
}

# Define the order of cities that satisfies all constraints
cities_order = [
    'Lyon',
    'Paris',
    'Copenhagen',
    'Santorini',
    'Oslo',
    'Krakow',
    'Helsinki',
    'Warsaw',
    'Riga',
    'Tallinn'
]

# Verify that each consecutive pair has a direct flight
for i in range(len(cities_order) - 1):
    current = cities_order[i]
    next_city = cities_order[i + 1]
    if next_city not in flights[current]:
        raise ValueError(f"No direct flight from {current} to {next_city}")

# Compute the day ranges
itinerary = []
start_day = 1
for city in cities_order:
    duration = cities_durations[city]
    end_day = start_day + duration - 1
    day_range = f"Day {start_day}-{end_day}"
    itinerary.append({'day_range': day_range, 'place': city})
    start_day = end_day

# Output as JSON
result = {'itinerary': itinerary}
print(json.dumps(result, indent=2))