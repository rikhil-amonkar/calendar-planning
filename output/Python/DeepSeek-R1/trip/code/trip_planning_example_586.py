import json

required_days = {
    'Prague': 2,
    'Helsinki': 4,
    'Frankfurt': 3,
    'Naples': 4,
    'Lyon': 3
}

flights = {
    'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
    'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
    'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
    'Lyon': ['Prague', 'Frankfurt'],
    'Naples': ['Helsinki', 'Frankfurt'],
}

cities_order = ['Prague', 'Helsinki', 'Naples', 'Frankfurt', 'Lyon']

valid = True
for i in range(len(cities_order) - 1):
    current = cities_order[i].lower()
    next_city = cities_order[i + 1].lower()
    if next_city not in [city.lower() for city in flights.get(cities_order[i], [])]:
        valid = False
        break

if valid:
    start_day = 1
    itinerary = []
    for city in cities_order:
        duration = required_days[city]
        end_day = start_day + duration - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = end_day
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))