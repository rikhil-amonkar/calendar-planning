import json
from z3 import *

# Define cities and required days
cities = {
    "Paris": 2,
    "Barcelona": 5,
    "Amsterdam": 2,
    "Warsaw": 4,
    "Venice": 3,
    "Vilnius": 3,
    "Hamburg": 4,
    "Salzburg": 4,
    "Florence": 5,
    "Tallinn": 2
}

# Define bidirectional flight connections
flight_routes = {
    "Paris": ["Barcelona", "Amsterdam", "Venice", "Hamburg", "Vilnius", "Florence", "Warsaw", "Tallinn"],
    "Barcelona": ["Paris", "Amsterdam", "Warsaw", "Hamburg", "Florence", "Venice", "Tallinn"],
    "Amsterdam": ["Paris", "Barcelona", "Warsaw", "Vilnius", "Hamburg", "Florence", "Venice", "Tallinn"],
    "Warsaw": ["Paris", "Barcelona", "Amsterdam", "Venice", "Vilnius", "Hamburg", "Tallinn"],
    "Venice": ["Paris", "Barcelona", "Amsterdam", "Warsaw", "Hamburg"],
    "Vilnius": ["Paris", "Amsterdam", "Warsaw", "Tallinn"],
    "Hamburg": ["Paris", "Barcelona", "Amsterdam", "Warsaw", "Venice", "Salzburg"],
    "Salzburg": ["Hamburg"],
    "Florence": ["Paris", "Barcelona", "Amsterdam"],
    "Tallinn": ["Paris", "Barcelona", "Amsterdam", "Warsaw", "Vilnius"]
}

# Create solver
s = Solver()

# Day variables (1-25)
day_vars = [Int(f"day_{d}") for d in range(1, 26)]
city_ids = {city: i for i, city in enumerate(cities.keys())}
id_to_city = {i: city for city, i in city_ids.items()}

# Each day must be a valid city
for day in day_vars:
    s.add(Or([day == city_ids[city] for city in cities]))

# Total days per city
for city, days_needed in cities.items():
    s.add(Sum([If(day_vars[d] == city_ids[city], 1, 0) for d in range(25)]) == days_needed)

# Fixed events
# Workshop in Paris on days 1-2
s.add(day_vars[0] == city_ids["Paris"])
s.add(day_vars[1] == city_ids["Paris"])

# Barcelona visit between days 3-6 (must have at least 1 day)
s.add(Or([day_vars[d] == city_ids["Barcelona"] for d in range(2, 6)]))

# Conference in Hamburg on days 19-22
for d in range(18, 22):
    s.add(day_vars[d] == city_ids["Hamburg"])

# Wedding in Salzburg on days 22-25
for d in range(21, 25):
    s.add(day_vars[d] == city_ids["Salzburg"])

# Tallinn visit between days 11-12
s.add(Or(day_vars[10] == city_ids["Tallinn"], day_vars[11] == city_ids["Tallinn"]))

# Flight connections between consecutive days
for i in range(24):
    current = day_vars[i]
    next_day = day_vars[i+1]
    s.add(Or(
        current == next_day,  # Stay in same city
        *[And(current == city_ids[city_from], next_day == city_ids[city_to])
          for city_from in flight_routes 
          for city_to in flight_routes[city_from]]
    ))

# Try to find solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for day in range(25):
        city_id = m.eval(day_vars[day]).as_long()
        itinerary.append({"day": day+1, "place": id_to_city[city_id]})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found")