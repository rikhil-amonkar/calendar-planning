import json

# Define trip constraints
madrid_days = 4
dublin_days = 3
tallinn_days = 2

# Define city order based on flight routes and constraints
cities_order = ['Madrid', 'Dublin', 'Tallinn']
city_days = {
    'Madrid': madrid_days,
    'Dublin': dublin_days,
    'Tallinn': tallinn_days
}

# Calculate itinerary
itinerary = []
current_start = 1

for city in cities_order:
    days = city_days[city]
    current_end = current_start + days - 1
    itinerary.append({
        'day_range': f"Day {current_start}-{current_end}",
        'place': city
    })
    current_start = current_end

# Format and output result
result = {'itinerary': itinerary}
print(json.dumps(result, indent=2))