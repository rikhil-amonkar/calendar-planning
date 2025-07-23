import json
from z3 import *

# Cities and their indices
cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
flight_connections = [
    ("Milan", "Stockholm"), ("Milan", "Munich"), ("Milan", "Seville"),
    ("Stockholm", "Tallinn"), ("Stockholm", "Munich"),
    ("Munich", "Bucharest"), ("Munich", "Seville"), ("Munich", "Tallinn"),
    ("Bucharest", "Munich"),
    ("Seville", "Munich"), ("Seville", "Milan"),
    ("Tallinn", "Stockholm"), ("Tallinn", "Munich")
]

# Required stay durations
required_days = {
    "Tallinn": 2,
    "Bucharest": 4,
    "Seville": 5,
    "Stockholm": 5,
    "Munich": 5,
    "Milan": 2
}

# Create solver
s = Solver()

# Variables: city for each day (1-18)
day_city = [Int(f"day_{day}_city") for day in range(1, 19)]

# Each day must be assigned to a valid city
for day in range(18):
    s.add(day_city[day] >= 0)
    s.add(day_city[day] < 6)

# Flight transitions must be direct
for day in range(17):
    current = day_city[day]
    next_day = day_city[day + 1]
    s.add(Or(
        current == next_day,  # Stay in same city
        *[And(current == city_to_idx[a], next_day == city_to_idx[b]) 
          for a, b in flight_connections]
    ))

# Special constraints for Bucharest, Munich, Seville
# Bucharest must be days 1-4 (inclusive)
for day in range(4):
    s.add(day_city[day] == city_to_idx["Bucharest"])

# Munich must be days 4-8 (inclusive)
for day in range(3, 8):
    s.add(day_city[day] == city_to_idx["Munich"])

# Seville must be days 8-12 (inclusive)
for day in range(7, 12):
    s.add(day_city[day] == city_to_idx["Seville"])

# Count days in each city (accounting for flight days)
for city in cities:
    count = 0
    for day in range(18):
        count += If(day_city[day] == city_to_idx[city], 1, 0)
    # Add extra day for Bucharest (flight day 4)
    if city == "Bucharest":
        count += If(day_city[3] == city_to_idx["Munich"], 1, 0)
    # Add extra day for Munich (flight day 4)
    if city == "Munich":
        count += If(day_city[3] == city_to_idx["Bucharest"], 1, 0)
    # Add extra day for Seville (flight day 8)
    if city == "Seville":
        count += If(day_city[7] == city_to_idx["Munich"], 1, 0)
    s.add(count == required_days[city])

# Solve and output
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(18):
        city_idx = model.evaluate(day_city[day]).as_long()
        itinerary.append({"day": day + 1, "place": cities[city_idx]})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found.")