import json
from z3 import *

# Define cities and required days
cities = {
    "Lyon": 3,
    "Paris": 5,
    "Riga": 2,
    "Berlin": 2,
    "Stockholm": 3,
    "Zurich": 5,
    "Nice": 2,
    "Seville": 3,
    "Milan": 3,
    "Naples": 4
}

# Define direct flight connections
direct_flights = {
    ("Paris", "Stockholm"),
    ("Seville", "Paris"),
    ("Naples", "Zurich"),
    ("Nice", "Riga"),
    ("Berlin", "Milan"),
    ("Paris", "Zurich"),
    ("Paris", "Nice"),
    ("Milan", "Paris"),
    ("Milan", "Riga"),
    ("Paris", "Lyon"),
    ("Milan", "Naples"),
    ("Paris", "Riga"),
    ("Berlin", "Stockholm"),
    ("Stockholm", "Riga"),
    ("Nice", "Zurich"),
    ("Milan", "Zurich"),
    ("Lyon", "Nice"),
    ("Zurich", "Stockholm"),
    ("Zurich", "Riga"),
    ("Berlin", "Naples"),
    ("Milan", "Stockholm"),
    ("Berlin", "Zurich"),
    ("Milan", "Seville"),
    ("Paris", "Naples"),
    ("Berlin", "Riga"),
    ("Nice", "Stockholm"),
    ("Berlin", "Paris"),
    ("Nice", "Naples"),
    ("Berlin", "Nice")
}

# Fix typo in Lyon
direct_flights.add(("Lyon", "Nice"))

# Create city mappings
city_names = sorted(cities.keys())
city_to_int = {city: idx for idx, city in enumerate(city_names)}
int_to_city = {idx: city for idx, city in enumerate(city_names)}

num_days = 23
s = Solver()

# Day variables
day = [Int(f"day_{i}") for i in range(num_days)]

# Each day must be a valid city
for d in day:
    s.add(And(d >= 0, d < len(city_names)))

# Fixed day constraints
s.add(day[0] == city_to_int["Berlin"])  # Day 1
s.add(day[1] == city_to_int["Berlin"])  # Day 2

s.add(day[19] == city_to_int["Stockholm"])  # Day 20
s.add(day[20] == city_to_int["Stockholm"])  # Day 21
s.add(day[21] == city_to_int["Stockholm"])  # Day 22

s.add(day[11] == city_to_int["Nice"])  # Day 12
s.add(day[12] == city_to_int["Nice"])  # Day 13

# Flight connection constraints
for i in range(num_days - 1):
    current = day[i]
    next_day = day[i + 1]
    flight_options = []
    for a, b in direct_flights:
        flight_options.append(And(current == city_to_int[a], next_day == city_to_int[b]))
        flight_options.append(And(current == city_to_int[b], next_day == city_to_int[a]))
    s.add(Or(*flight_options))

# Total days per city
for city, req_days in cities.items():
    city_idx = city_to_int[city]
    s.add(Sum([If(d == city_idx, 1, 0) for d in day]) == req_days)

# Solve
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(num_days):
        city_idx = model.evaluate(day[i]).as_long()
        itinerary.append({"day": i + 1, "place": int_to_city[city_idx]})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found - try adjusting constraints")