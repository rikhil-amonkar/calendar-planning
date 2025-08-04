import json
from z3 import *

# Define the cities
cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]

# Define direct flights as adjacency list
direct_flights = {
    "Oslo": ["Split", "Reykjavik", "Frankfurt", "Bucharest", "Stockholm", "Munich", "Barcelona"],
    "Reykjavik": ["Oslo", "Munich", "Frankfurt", "Barcelona", "Stockholm"],
    "Stockholm": ["Barcelona", "Reykjavik", "Munich", "Oslo", "Frankfurt", "Split"],
    "Munich": ["Reykjavik", "Frankfurt", "Bucharest", "Oslo", "Stockholm", "Barcelona", "Split"],
    "Frankfurt": ["Munich", "Oslo", "Barcelona", "Reykjavik", "Bucharest", "Stockholm", "Split"],
    "Barcelona": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Split", "Oslo", "Munich"],
    "Bucharest": ["Munich", "Barcelona", "Oslo", "Frankfurt"],
    "Split": ["Oslo", "Barcelona", "Stockholm", "Frankfurt", "Munich"]
}

# Days
days = 20

# Create a Z3 solver
s = Solver()

# Create variables: day[i] is the city visited on day i+1 (since days start at 1)
day_vars = [Int(f"day_{i}") for i in range(days)]

# Each day variable must be between 0 and 7 (representing the 8 cities)
for d in day_vars:
    s.add(d >= 0, d < len(cities))

# Function to get city index
def city_index(city):
    return cities.index(city)

# Duration constraints
durations = {
    "Oslo": 2,
    "Reykjavik": 5,
    "Stockholm": 4,
    "Munich": 4,
    "Frankfurt": 4,
    "Barcelona": 3,
    "Bucharest": 2,
    "Split": 3
}

# For each city, the sum of days where day_vars equals its index must be its duration
for city in cities:
    idx = city_index(city)
    s.add(Sum([If(day_vars[i] == idx, 1, 0) for i in range(days)]) == durations[city])

# Specific constraints:
# 1. Oslo: 2 days, with one visit during day 16-17 (inclusive)
oslo_idx = city_index("Oslo")
s.add(Or(day_vars[15] == oslo_idx, day_vars[16] == oslo_idx))  # days 16 and 17 are indices 15 and 16

# 2. Reykjavik: 5 days, meet friend between day 9-13 (so at least one day in 9-13)
reykjavik_idx = city_index("Reykjavik")
s.add(Sum([If(And(day_vars[i] == reykjavik_idx, i >= 8, i <= 12), 1, 0) for i in range(days)]) >= 1)  # days 9-13 are indices 8-12

# 3. Munich: 4 days, visit relatives between day 13-16 (so at least one day in 13-16)
munich_idx = city_index("Munich")
s.add(Sum([If(And(day_vars[i] == munich_idx, i >= 12, i <= 15), 1, 0) for i in range(days)]) >= 1)  # days 13-16 are indices 12-15

# 4. Frankfurt: 4 days, workshop between day 17-20 (so at least one day in 17-20)
frankfurt_idx = city_index("Frankfurt")
s.add(Sum([If(And(day_vars[i] == frankfurt_idx, i >= 16, i < 20), 1, 0) for i in range(days)]) >= 1)  # days 17-20 are indices 16-19

# Flight constraints: consecutive days must be same city or connected by direct flight
for i in range(days - 1):
    current_city_var = day_vars[i]
    next_city_var = day_vars[i + 1]
    # Either same city or connected by direct flight
    current_city = cities[m[day_vars[i]].as_long()] if s.check() == sat else None
    next_city = cities[m[day_vars[i + 1]].as_long()] if s.check() == sat else None
    if current_city and next_city and current_city != next_city:
        s.add(next_city in direct_flights[current_city])

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(days):
        city_idx = m.evaluate(day_vars[i]).as_long()
        itinerary.append({"day": i + 1, "place": cities[city_idx]})
    
    # Convert to the required JSON format
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")