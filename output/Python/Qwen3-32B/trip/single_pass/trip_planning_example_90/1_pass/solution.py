import itertools
import json

# Define input parameters
total_days = 17
durations = {
    'Vilnius': 7,
    'Naples': 5,
    'Vienna': 7
}
direct_flights = {('Naples', 'Vienna'), ('Vienna', 'Naples'), ('Vienna', 'Vilnius'), ('Vilnius', 'Vienna')}
relatives_constraint = {
    'city': 'Naples',
    'start_day': 1,
    'end_day': 5
}
cities = ['Naples', 'Vienna', 'Vilnius']

# Generate all valid routes
valid_routes = []
for perm in itertools.permutations(cities):
    valid = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            valid = False
            break
    if valid:
        valid_routes.append(perm)

# Find the correct route that satisfies the relatives constraint
itinerary_route = None
for route in valid_routes:
    city_day_ranges = {}
    current_start = 1
    for city in route:
        duration = durations[city]
        end_day = current_start + duration - 1
        city_day_ranges[city] = (current_start, end_day)
        current_start = end_day  # next city starts on this day (flight day)
    # Check if Naples is within the relatives' days
    naples_range = city_day_ranges.get('Naples', (None, None))
    if naples_range[0] is not None and naples_range[1] is not None:
        if (naples_range[0] >= relatives_constraint['start_day'] and 
            naples_range[1] <= relatives_constraint['end_day']):
            itinerary_route = route
            break

# Generate the itinerary
itinerary = []
if itinerary_route:
    city_day_ranges = {}
    current_start = 1
    for city in itinerary_route:
        duration = durations[city]
        end_day = current_start + duration - 1
        city_day_ranges[city] = (current_start, end_day)
        current_start = end_day  # prepare for next city
    for city in itinerary_route:
        start, end = city_day_ranges[city]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))