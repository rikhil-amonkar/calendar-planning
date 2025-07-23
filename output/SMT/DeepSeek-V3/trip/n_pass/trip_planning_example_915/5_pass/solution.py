import json
from z3 import *

# Define cities and their codes
cities = {
    "Bucharest": 0,
    "Venice": 1,
    "Prague": 2,
    "Frankfurt": 3,
    "Zurich": 4,
    "Florence": 5,
    "Tallinn": 6
}

reverse_cities = {v: k for k, v in cities.items()}

# Direct flights as adjacency list
direct_flights = {
    0: [3, 2, 4],  # Bucharest
    1: [3, 4],      # Venice
    2: [6, 4, 5, 3, 0],  # Prague
    3: [0, 1, 6, 4, 5, 2],  # Frankfurt
    4: [5, 1, 0, 6, 3, 2],   # Zurich
    5: [2, 3, 4],   # Florence
    6: [2, 3, 4]    # Tallinn
}

# Create Z3 variables for each day (1..26)
days = 26
day_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

solver = Solver()

# Each day must be assigned to a valid city
for day in day_vars:
    solver.add(Or([day == city_code for city_code in cities.values()]))

# Add constraints for fixed stays
# Venice: days 22-26 (wedding)
for day in range(22, 27):
    solver.add(day_vars[day - 1] == cities["Venice"])

# Frankfurt: days 12-16 (annual show)
for day in range(12, 17):
    solver.add(day_vars[day - 1] == cities["Frankfurt"])

# Tallinn: days 8-12 (meet friends)
for day in range(8, 13):
    solver.add(day_vars[day - 1] == cities["Tallinn"])

# Total stay constraints
solver.add(Sum([If(day == cities["Bucharest"], 1, 0) for day in day_vars]) == 3)
solver.add(Sum([If(day == cities["Venice"], 1, 0) for day in day_vars]) == 5)
solver.add(Sum([If(day == cities["Prague"], 1, 0) for day in day_vars]) == 4)
solver.add(Sum([If(day == cities["Frankfurt"], 1, 0) for day in day_vars]) == 5)
solver.add(Sum([If(day == cities["Zurich"], 1, 0) for day in day_vars]) == 5)
solver.add(Sum([If(day == cities["Florence"], 1, 0) for day in day_vars]) == 5)
solver.add(Sum([If(day == cities["Tallinn"], 1, 0) for day in day_vars]) == 5)

# Flight constraints between consecutive days
for i in range(days - 1):
    current = day_vars[i]
    next_day = day_vars[i + 1]
    solver.add(Or(
        current == next_day,  # Stay in same city
        Or([And(current == from_city, next_day == to_city)
           for from_city in direct_flights
           for to_city in direct_flights[from_city]])
    ))

# Try to find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, days + 1):
        city_code = model.evaluate(day_vars[day - 1]).as_long()
        city_name = reverse_cities[city_code]
        itinerary.append({"day": day, "place": city_name})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")