import json
from z3 import *

# Define the cities and their required days
cities = {
    "Berlin": 3,
    "Nice": 5,
    "Athens": 5,
    "Stockholm": 5,
    "Barcelona": 2,
    "Vilnius": 4,
    "Lyon": 2
}

# Corrected direct flight connections
direct_flights = {
    "Lyon": ["Nice", "Barcelona"],
    "Nice": ["Lyon", "Athens", "Berlin", "Barcelona", "Stockholm"],
    "Athens": ["Nice", "Stockholm", "Berlin", "Vilnius", "Barcelona"],
    "Stockholm": ["Athens", "Berlin", "Nice", "Barcelona"],
    "Berlin": ["Nice", "Athens", "Barcelona", "Vilnius", "Stockholm"],
    "Barcelona": ["Berlin", "Nice", "Athens", "Stockholm", "Lyon"],
    "Vilnius": ["Berlin", "Athens"],
    "Lyon": ["Nice", "Barcelona"]
}

# Create solver
s = Solver()

# Days 1-20
days = 20
day_city = [Int(f"day_{i}") for i in range(1, days + 1)]

# City to ID mapping
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Each day must be one of the cities
for day in day_city:
    s.add(Or([day == city_ids[city] for city in cities]))

# Fixed constraints:
# Berlin: day 1 and 3
s.add(day_city[0] == city_ids["Berlin"])  # day 1
s.add(day_city[2] == city_ids["Berlin"])  # day 3

# Barcelona workshop between day 3-4 (day 4 must be Barcelona)
s.add(day_city[3] == city_ids["Barcelona"])  # day 4

# Lyon wedding between day 4-5 (day 5 must be Lyon)
s.add(day_city[4] == city_ids["Lyon"])  # day 5

# Transition constraints
for i in range(days - 1):
    current = day_city[i]
    next_day = day_city[i + 1]
    s.add(Or(
        current == next_day,  # Stay in same city
        *[And(current == city_ids[c1], next_day == city_ids[c2]) 
          for c1 in cities 
          for c2 in direct_flights.get(c1, [])]
    ))

# Total days per city
for city, days_needed in cities.items():
    s.add(Sum([If(day == city_ids[city], 1, 0) for day in day_city]) == days_needed)

# Try to find a solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(days):
        day_num = i + 1
        city_id = m.evaluate(day_city[i]).as_long()
        city_name = id_to_city[city_id]
        itinerary.append({"day": day_num, "place": city_name})
    
    # Verify all constraints are met
    city_counts = {city: 0 for city in cities}
    for entry in itinerary:
        city_counts[entry["place"]] += 1
    
    valid = True
    for city, count in city_counts.items():
        if count != cities[city]:
            valid = False
            break
    
    if valid:
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("Found solution but constraints not fully satisfied")
else:
    print("No valid itinerary found")