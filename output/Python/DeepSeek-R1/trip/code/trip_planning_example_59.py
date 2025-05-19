import json

# Input parameters
total_days = 16
cities_days = {'Bucharest': 7, 'Lyon': 7, 'Porto': 4}
wedding_range = (1, 7)
flight_routes = [('Bucharest', 'Lyon'), ('Lyon', 'Porto')]

# Build flight graph
flight_graph = {}
for a, b in flight_routes:
    flight_graph.setdefault(a, []).append(b)
    flight_graph.setdefault(b, []).append(a)

# Determine city order starting with Bucharest due to wedding
order = ['Bucharest']
remaining = set(cities_days.keys()) - {'Bucharest'}
current = 'Bucharest'

while remaining:
    neighbors = flight_graph.get(current, [])
    next_city = next((c for c in neighbors if c in remaining), None)
    if next_city is None:
        raise ValueError("No valid itinerary")
    order.append(next_city)
    remaining.remove(next_city)
    current = next_city

# Calculate day ranges
itinerary = []
current_day = 1
for city in order:
    days = cities_days[city]
    end_day = current_day + days - 1
    itinerary.append({
        'day_range': f'Day {current_day}-{end_day}',
        'place': city
    })
    current_day = end_day

# Validate total days
if current_day > total_days:
    raise ValueError("Invalid duration")

print(json.dumps({'itinerary': itinerary}))