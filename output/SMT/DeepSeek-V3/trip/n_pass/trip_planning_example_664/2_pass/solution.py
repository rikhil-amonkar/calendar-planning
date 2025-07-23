import json
from z3 import *

# Cities
cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Direct flights: adjacency list
direct_flights = {
    "Milan": ["Stockholm", "Munich", "Seville"],
    "Stockholm": ["Milan", "Munich", "Tallinn"],
    "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
    "Bucharest": ["Munich"],
    "Seville": ["Munich", "Milan"],
    "Tallinn": ["Stockholm", "Munich"]
}

# Create a set of allowed transitions (A, B) meaning you can fly from A to B
allowed_transitions = set()
for city, connections in direct_flights.items():
    for connected_city in connections:
        allowed_transitions.add((city, connected_city))

# Required stays
required_days = {
    "Tallinn": 2,
    "Bucharest": 4,
    "Seville": 5,
    "Stockholm": 5,
    "Munich": 5,
    "Milan": 2
}

# Z3 solver setup
s = Solver()

# Variables: for each day (1..18), which city are you in?
day_city = [Int(f"day_{day}_city") for day in range(1, 19)]  # days 1..18

# Each day_city variable must be between 0 and 5 (index of cities)
for day in range(18):
    s.add(day_city[day] >= 0)
    s.add(day_city[day] < 6)

# Constraints for transitions: if day changes city, must be a direct flight
for day in range(17):  # from day 1 to day 17 (since next day is day+1)
    current_city = day_city[day]
    next_city = day_city[day + 1]
    # Either stay in the same city, or move to a connected city
    s.add(Or(
        current_city == next_city,
        *[
            And(current_city == city_to_idx[a], next_city == city_to_idx[b])
            for a, b in allowed_transitions
        ]
    ))

# Constraints for required days in each city
for city in cities:
    total_days = Sum([If(day_city[day] == city_to_idx[city], 1, 0) for day in range(18)])
    s.add(total_days == required_days[city])

# Specific constraints:
# Bucharest between day 1 and day 4 (inclusive)
for day in range(0, 4):  # days 1-4 (indices 0-3)
    s.add(day_city[day] == city_to_idx["Bucharest"])

# Munich wedding between day 4 and day 8 (days 5-8 in 1-based, 4-7 in 0-based)
for day in range(4, 8):  # days 5-8 (indices 4-7)
    s.add(day_city[day] == city_to_idx["Munich"])

# Seville friends between day 8 and 12 (days 9-12 in 1-based, 8-11 in 0-based)
for day in range(8, 12):  # days 9-12 (indices 8-11)
    s.add(day_city[day] == city_to_idx["Seville"])

# Check and get model
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(18):
        city_idx = model.evaluate(day_city[day]).as_long()
        itinerary.append({"day": day + 1, "place": cities[city_idx]})
    
    # Prepare the output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")