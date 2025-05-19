import json

required_days = {
    'Mykonos': 6,
    'Budapest': 3,
    'Hamburg': 2
}
fixed_mykonos = [4, 9]
flight_connections = {
    'Hamburg': ['Budapest'],
    'Budapest': ['Hamburg', 'Mykonos'],
    'Mykonos': ['Budapest']
}

itinerary = []

# Assign Mykonos
myk_start = min(fixed_mykonos)
myk_end = max(fixed_mykonos)
itinerary.append({'day_range': f'Day {myk_start}-{myk_end}', 'place': 'Mykonos'})

# Assign Budapest
budapest_end = myk_start
budapest_start = budapest_end - required_days['Budapest'] + 1
itinerary.insert(0, {'day_range': f'Day {budapest_start}-{budapest_end}', 'place': 'Budapest'})

# Assign Hamburg
hamburg_end = budapest_start
hamburg_start = max(1, hamburg_end - required_days['Hamburg'] + 1)
itinerary.insert(0, {'day_range': f'Day {hamburg_start}-{hamburg_end}', 'place': 'Hamburg'})

# Validate transitions
prev_city = None
valid = True
for entry in itinerary:
    current_city = entry['place']
    if prev_city and current_city not in flight_connections.get(prev_city, []):
        valid = False
        break
    prev_city = current_city

if valid:
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No valid itinerary found"}))