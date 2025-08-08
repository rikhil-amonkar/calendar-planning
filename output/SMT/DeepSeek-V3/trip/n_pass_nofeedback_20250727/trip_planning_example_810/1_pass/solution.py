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

# Direct flight connections
direct_flights = {
    "Lyon": ["Nice"],
    "Nice": ["Lyon", "Athens", "Berlin", "Barcelona", "Stockholm"],
    "Athens": ["Nice", "Stockholm", "Berlin", "Vilnius", "Barcelona"],
    "Stockholm": ["Athens", "Berlin", "Nice", "Barcelona"],
    "Berlin": ["Nice", "Athens", "Barcelona", "Vilnius", "Stockholm"],
    "Barcelona": ["Berlin", "Nice", "Athens", "Stockholm", "Lyon"],
    "Vilnius": ["Berlin", "Athens"],
    "Lyon": ["Nice", "Barcelona"]
}

# Create a solver instance
s = Solver()

# Create variables for each day (1..20)
days = 20
day_city = [Int(f"day_{i}") for i in range(1, days + 1)]

# Assign each day_city to a numerical representation of the cities
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraint: each day must be one of the cities
for day in day_city:
    s.add(Or([day == city_ids[city] for city in cities))

# Fixed constraints:
# Berlin: day 1 and 3
s.add(day_city[0] == city_ids["Berlin"])  # day 1
s.add(day_city[2] == city_ids["Berlin"])  # day 3

# Barcelona: workshop between day 3 and 4 (so day 3 or 4 must be Barcelona)
# Since day 3 is Berlin, day 4 must be Barcelona
s.add(day_city[3] == city_ids["Barcelona"])  # day 4

# Lyon: wedding between day 4 and 5. So day 4 or 5 must be Lyon. But day 4 is Barcelona, so day 5 is Lyon
s.add(day_city[4] == city_ids["Lyon"])  # day 5

# Constraint for transitions: consecutive days must be the same city or connected by direct flight
for i in range(days - 1):
    current_city = day_city[i]
    next_city = day_city[i + 1]
    # Either stay in the same city or move to a connected city
    s.add(Or(
        current_city == next_city,
        *[
            And(current_city == city_ids[city1], next_city == city_ids[city2])
            for city1 in cities
            for city2 in direct_flights.get(city1, [])
        ]
    ))

# Constraints for total days per city
for city, total_days in cities.items():
    s.add(Sum([If(day == city_ids[city], 1, 0) for day in day_city]) == total_days)

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(days):
        day_num = i + 1
        city_id = model.evaluate(day_city[i]).as_long()
        city_name = id_to_city[city_id]
        itinerary.append({"day": day_num, "place": city_name})
    
    # Prepare the output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")