import json

# Define cities and their required durations
durations = {
    'Hamburg': 2,
    'Dublin': 5,
    'Helsinki': 4,
    'Reykjavik': 2,
    'London': 5,
    'Mykonos': 3
}

# Define direct flight connections as a set of bidirectional pairs
flight_connections = {
    ('Dublin', 'London'),
    ('Hamburg', 'Dublin'),
    ('Helsinki', 'Reykjavik'),
    ('Hamburg', 'London'),
    ('Dublin', 'Helsinki'),
    ('Reykjavik', 'London'),
    ('London', 'Mykonos'),
    ('Dublin', 'Reykjavik'),
    ('Hamburg', 'Helsinki'),
    ('Helsinki', 'London'),
}

def is_direct_flight(city1, city2):
    return (city1, city2) in flight_connections or (city2, city1) in flight_connections

# Determine the order of cities based on constraints
cities_order = ['Hamburg', 'Dublin', 'Helsinki', 'Reykjavik', 'London', 'Mykonos']

# Validate flight connections between consecutive cities
for i in range(len(cities_order) - 1):
    city_a = cities_order[i]
    city_b = cities_order[i + 1]
    if not is_direct_flight(city_a, city_b):
        raise ValueError(f"No direct flight between {city_a} and {city_b}")

# Compute the itinerary day ranges
itinerary = []
current_day = 1
for city in cities_order:
    duration = durations[city]
    end_day = current_day + duration - 1
    day_range = f"Day {current_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_day = end_day  # Next city starts on this day

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))