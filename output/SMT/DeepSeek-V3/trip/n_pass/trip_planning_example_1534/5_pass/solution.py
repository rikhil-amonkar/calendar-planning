import json
from z3 import *

# Define the cities
cities = [
    "Warsaw", "Venice", "Vilnius", "Salzburg", "Amsterdam", 
    "Barcelona", "Paris", "Hamburg", "Florence", "Tallinn"
]

# Direct flights as a dictionary: key is source, value is list of destinations
direct_flights = {
    "Paris": ["Venice", "Amsterdam", "Vilnius", "Florence", "Hamburg", "Warsaw", "Tallinn", "Barcelona"],
    "Venice": ["Paris", "Warsaw", "Amsterdam", "Barcelona", "Hamburg"],
    "Amsterdam": ["Barcelona", "Warsaw", "Vilnius", "Hamburg", "Florence", "Venice", "Tallinn", "Paris"],
    "Barcelona": ["Amsterdam", "Warsaw", "Hamburg", "Florence", "Venice", "Tallinn", "Paris"],
    "Warsaw": ["Amsterdam", "Barcelona", "Venice", "Vilnius", "Tallinn", "Hamburg", "Paris"],
    "Vilnius": ["Amsterdam", "Warsaw", "Paris", "Tallinn"],
    "Hamburg": ["Amsterdam", "Barcelona", "Paris", "Venice", "Warsaw", "Salzburg"],
    "Florence": ["Barcelona", "Amsterdam", "Paris"],
    "Tallinn": ["Barcelona", "Warsaw", "Vilnius", "Amsterdam", "Paris"],
    "Salzburg": ["Hamburg"]
}

# Create a Z3 solver instance
s = Solver()

# Create variables for each day (1..25), each is an integer representing a city index
day_vars = [Int(f"day_{i}") for i in range(1, 26)]

# Constraint: each day_var is between 0 and 9 (indices of cities)
for day in day_vars:
    s.add(day >= 0, day < len(cities))

# Duration constraints: each city must be visited for exactly the specified days
duration_constraints = {
    "Warsaw": 4,
    "Venice": 3,
    "Vilnius": 3,
    "Salzburg": 4,
    "Amsterdam": 2,
    "Barcelona": 5,
    "Paris": 2,
    "Hamburg": 4,
    "Florence": 5,
    "Tallinn": 2
}

# For each city, count the number of days it appears in day_vars and set equal to duration
for city_idx, city in enumerate(cities):
    duration = duration_constraints[city]
    s.add(Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(25)]) == duration)

# Event constraints:
# Salzburg between day 22 and 25 (inclusive)
for day in [21, 22, 23, 24]:  # days 22-25 (0-based 21-24)
    s.add(day_vars[day] == cities.index("Salzburg"))

# Barcelona between day 2 and 6 (meet friends). At least one day in this range must be Barcelona.
s.add(Or([day_vars[i] == cities.index("Barcelona") for i in range(1, 6)]))  # days 2-6 (1-5 in 0-based)

# Paris workshop between day 1 and 2. So day 0 and 1 (0-based) must be Paris.
s.add(day_vars[0] == cities.index("Paris"))
s.add(day_vars[1] == cities.index("Paris"))

# Hamburg conference between day 19 and 22 (0-based 18-21). But Salzburg is 22-25, so Hamburg must be 19-21.
for day in [18, 19, 20]:  # days 19, 20, 21 (0-based 18,19,20)
    s.add(day_vars[day] == cities.index("Hamburg"))

# Tallinn meet friend between day 11 and 12 (0-based 10-11)
s.add(Or(day_vars[10] == cities.index("Tallinn"), day_vars[11] == cities.index("Tallinn")))

# Flight constraints: consecutive days must be same city or have a direct flight
for i in range(24):  # for day i and i+1 (0-based)
    current_city = day_vars[i]
    next_city = day_vars[i+1]
    # Either same city, or there's a flight
    s.add(Or(
        current_city == next_city,
        And(current_city != next_city, 
            Or([And(current_city == city_idx, next_city == cities.index(dest)) 
               for city_idx, city in enumerate(cities) 
               for dest in direct_flights.get(city, [])]))
    ))

# Check if the solver is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(25):
        city_idx = model.evaluate(day_vars[day]).as_long()
        itinerary.append({"day": day + 1, "place": cities[city_idx]})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found.")