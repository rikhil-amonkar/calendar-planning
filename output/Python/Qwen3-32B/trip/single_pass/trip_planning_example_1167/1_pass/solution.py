import json

# Define direct flights as a set of tuples (both directions)
direct_flight_pairs = {
    ('Dublin', 'Brussels'),
    ('Brussels', 'Dublin'),
    ('Mykonos', 'Naples'),
    ('Naples', 'Mykonos'),
    ('Venice', 'Istanbul'),
    ('Istanbul', 'Venice'),
    ('Frankfurt', 'Krakow'),
    ('Krakow', 'Frankfurt'),
    ('Naples', 'Dublin'),
    ('Dublin', 'Naples'),
    ('Krakow', 'Brussels'),
    ('Brussels', 'Krakow'),
    ('Naples', 'Istanbul'),
    ('Istanbul', 'Naples'),
    ('Naples', 'Brussels'),
    ('Brussels', 'Naples'),
    ('Istanbul', 'Frankfurt'),
    ('Frankfurt', 'Istanbul'),
    ('Brussels', 'Frankfurt'),
    ('Frankfurt', 'Brussels'),
    ('Istanbul', 'Krakow'),
    ('Krakow', 'Istanbul'),
    ('Istanbul', 'Brussels'),
    ('Brussels', 'Istanbul'),
    ('Venice', 'Frankfurt'),
    ('Frankfurt', 'Venice'),
    ('Naples', 'Frankfurt'),
    ('Frankfurt', 'Naples'),
    ('Dublin', 'Frankfurt'),
    ('Frankfurt', 'Dublin'),
    ('Venice', 'Brussels'),
    ('Brussels', 'Venice'),
    ('Naples', 'Venice'),
    ('Venice', 'Naples'),
    ('Istanbul', 'Dublin'),
    ('Dublin', 'Istanbul'),
    ('Venice', 'Dublin'),
    ('Dublin', 'Venice'),
    ('Dublin', 'Krakow'),
    ('Krakow', 'Dublin'),
}

# Define cities with their durations and fixed start days
cities = {
    'Mykonos': {'duration': 4, 'fixed_start': 1},
    'Istanbul': {'duration': 3, 'fixed_start': 9},
    'Dublin': {'duration': 5, 'fixed_start': 11},
    'Frankfurt': {'duration': 3, 'fixed_start': 15},
    'Naples': {'duration': 4},
    'Venice': {'duration': 3},
    'Krakow': {'duration': 4},
    'Brussels': {'duration': 2},
}

# Define the itinerary order
itinerary_order = ['Mykonos', 'Naples', 'Venice', 'Istanbul', 'Dublin', 'Frankfurt', 'Krakow', 'Brussels']

# Check if all transitions are valid
for i in range(len(itinerary_order) - 1):
    current_city = itinerary_order[i]
    next_city = itinerary_order[i + 1]
    if (current_city, next_city) not in direct_flight_pairs:
        raise ValueError(f"No direct flight from {current_city} to {next_city}")

# Calculate the itinerary with day ranges
itinerary = []
prev_end = 0
for city_name in itinerary_order:
    city_info = cities[city_name]
    if 'fixed_start' in city_info:
        start_day = city_info['fixed_start']
        # Ensure that the fixed start is after the previous city's end
        if start_day < prev_end:
            raise ValueError(f"Fixed start day for {city_name} ({start_day}) is before previous city's end day ({prev_end})")
    else:
        start_day = prev_end
    duration = city_info['duration']
    end_day = start_day + duration - 1
    day_range = f"Day {start_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city_name})
    prev_end = end_day

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))