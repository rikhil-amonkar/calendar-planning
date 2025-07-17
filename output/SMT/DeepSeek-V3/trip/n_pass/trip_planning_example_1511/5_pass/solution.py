from z3 import *

# Define the cities
cities = {
    "Venice": 0,
    "Reykjavik": 1,
    "Munich": 2,
    "Santorini": 3,
    "Manchester": 4,
    "Porto": 5,
    "Bucharest": 6,
    "Tallinn": 7,
    "Valencia": 8,
    "Vienna": 9
}

# Inverse mapping for cities
city_names = {v: k for k, v in cities.items()}

# Direct flights: adjacency list
flights = {
    0: [2, 3, 4, 9],  # Venice
    1: [9, 2],         # Reykjavik
    2: [0, 5, 4, 1, 9, 7, 6, 8],  # Munich
    3: [4, 0, 9, 6],   # Santorini
    4: [6, 3, 9, 5, 0, 2],  # Manchester
    5: [2, 9, 4, 8],   # Porto
    6: [4, 8, 9, 2, 3],  # Bucharest
    7: [2],           # Tallinn
    8: [9, 5, 6, 2],  # Valencia
    9: [1, 8, 4, 5, 0, 3, 2, 6]  # Vienna
}

# Days to spend in each city
required_days = {
    "Venice": 3,
    "Reykjavik": 2,
    "Munich": 3,
    "Santorini": 3,
    "Manchester": 3,
    "Porto": 3,
    "Bucharest": 5,
    "Tallinn": 4,
    "Valencia": 2,
    "Vienna": 5
}

# Fixed constraints
fixed_constraints = [
    (2, 4, 6),  # Munich from day 4 to 6 (inclusive)
    (3, 8, 10), # Santorini between day 8 and 10 (inclusive)
    (8, 14, 15) # Valencia between day 14 and 15 (inclusive)
]

# Initialize Z3 solver
s = Solver()

# Create variables for each day (1..24)
day_vars = [Int(f"day_{i}") for i in range(1, 25)]

# Each day must be one of the cities
for day in day_vars:
    s.add(Or([day == c for c in cities.values()]))

# Add fixed constraints
for city, start, end in fixed_constraints:
    for d in range(start, end + 1):
        s.add(day_vars[d-1] == city)

# Ensure required days per city
for city, days in required_days.items():
    city_code = cities[city]
    s.add(Sum([If(day_vars[i] == city_code, 1, 0) for i in range(24)]) == days)

# Flight constraints: consecutive days must be same city or connected by a direct flight
for i in range(23):
    current_day = day_vars[i]
    next_day = day_vars[i+1]
    s.add(Or(
        current_day == next_day,
        And(current_day != next_day, 
            Or([next_day == flight for flight in flights[current_day.as_long()]]))
    ))

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(24):
        day = i + 1
        city_code = m.evaluate(day_vars[i]).as_long()
        city_name = city_names[city_code]
        itinerary.append({"day": day, "place": city_name})
    print({"itinerary": itinerary})
else:
    print("No valid itinerary found.")