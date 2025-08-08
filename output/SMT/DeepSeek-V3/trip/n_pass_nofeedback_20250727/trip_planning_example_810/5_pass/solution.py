import json
from z3 import *

# Define cities and required days
cities = {
    "Berlin": 3,
    "Nice": 5,
    "Athens": 5,
    "Stockholm": 5,
    "Barcelona": 2,
    "Vilnius": 4,
    "Lyon": 2
}

# Enhanced flight connections (more flexible)
direct_flights = {
    "Berlin": ["Nice", "Athens", "Barcelona", "Stockholm", "Vilnius"],
    "Nice": ["Berlin", "Athens", "Barcelona", "Lyon", "Stockholm"],
    "Athens": ["Berlin", "Nice", "Stockholm", "Vilnius", "Barcelona"],
    "Stockholm": ["Berlin", "Nice", "Athens", "Barcelona"],
    "Barcelona": ["Berlin", "Nice", "Athens", "Stockholm", "Lyon"],
    "Vilnius": ["Berlin", "Athens"],
    "Lyon": ["Nice", "Barcelona"]
}

s = Solver()

# Create day variables (1-20)
day_city = [Int(f"day_{i}") for i in range(1, 21)]

# City ID mapping
city_ids = {city: idx for idx, city in enumerate(cities)}
id_to_city = {v: k for k, v in city_ids.items()}

# Each day must be one of the cities
for day in day_city:
    s.add(Or([day == city_ids[city] for city in cities]))

# Fixed constraints
s.add(day_city[0] == city_ids["Berlin"])  # Day 1: Berlin
s.add(day_city[2] == city_ids["Berlin"])  # Day 3: Berlin
s.add(day_city[3] == city_ids["Barcelona"])  # Day 4: Barcelona
s.add(day_city[4] == city_ids["Lyon"])    # Day 5: Lyon

# Transition constraints
for i in range(19):
    current = day_city[i]
    next_day = day_city[i+1]
    s.add(Or(
        current == next_day,  # Stay in same city
        *[And(current == city_ids[c1], next_day == city_ids[c2])
          for c1 in cities 
          for c2 in direct_flights[c1]]
    ))

# Total days per city
for city, days_needed in cities.items():
    s.add(Sum([If(day == city_ids[city], 1, 0) for day in day_city) == days_needed)

# Try to find solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    city_days = {city: 0 for city in cities}
    
    for i in range(20):
        day_num = i + 1
        city_id = m.evaluate(day_city[i]).as_long()
        city_name = id_to_city[city_id]
        itinerary.append({"day": day_num, "place": city_name})
        city_days[city_name] += 1
    
    # Verify all constraints
    valid = all(city_days[city] == cities[city] for city in cities)
    
    if valid:
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("Solution found but doesn't meet all constraints")
else:
    print("No valid itinerary found that satisfies all constraints")