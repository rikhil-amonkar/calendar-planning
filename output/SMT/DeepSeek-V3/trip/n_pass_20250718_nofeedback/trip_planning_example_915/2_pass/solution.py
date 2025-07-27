import json
from z3 import *

# Define the cities and their codes
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
    0: [3, 2, 4],  # Bucharest: Frankfurt, Prague, Zurich
    1: [3, 4],      # Venice: Frankfurt, Zurich
    2: [6, 4, 5, 3, 0],  # Prague: Tallinn, Zurich, Florence, Frankfurt, Bucharest
    3: [0, 1, 6, 4, 5, 2],  # Frankfurt: Bucharest, Venice, Tallinn, Zurich, Florence, Prague
    4: [5, 1, 0, 6, 3, 2],   # Zurich: Florence, Venice, Bucharest, Tallinn, Frankfurt, Prague
    5: [2, 3, 4],   # Florence: Prague, Frankfurt, Zurich
    6: [2, 3, 4]    # Tallinn: Prague, Frankfurt, Zurich
}

# Create Z3 variables for each day (1..26)
days = 26
day_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

solver = Solver()

# Each day variable must be one of the city codes
for day in day_vars:
    solver.add(Or([day == city_code for city_code in cities.values()]))

# Add constraints for fixed stays
# Bucharest for 3 days (anywhere)
solver.add(Sum([If(day == cities["Bucharest"], 1, 0) for day in day_vars]) == 3)

# Venice: 5 days total, and between day 22-26 must be in Venice
solver.add(Sum([If(day == cities["Venice"], 1, 0) for day in day_vars]) == 5)
for day in range(22, 27):
    solver.add(day_vars[day - 1] == cities["Venice"])

# Prague: 4 days
solver.add(Sum([If(day == cities["Prague"], 1, 0) for day in day_vars]) == 4)

# Frankfurt: 5 days, and between day 12-16 must be in Frankfurt
solver.add(Sum([If(day == cities["Frankfurt"], 1, 0) for day in day_vars]) == 5)
for day in range(12, 17):
    solver.add(day_vars[day - 1] == cities["Frankfurt"])

# Zurich: 5 days
solver.add(Sum([If(day == cities["Zurich"], 1, 0) for day in day_vars]) == 5)

# Florence: 5 days
solver.add(Sum([If(day == cities["Florence"], 1, 0) for day in day_vars]) == 5)

# Tallinn: 5 days, and between day 8-12 must be in Tallinn
solver.add(Sum([If(day == cities["Tallinn"], 1, 0) for day in day_vars]) == 5)
for day in range(8, 13):
    solver.add(day_vars[day - 1] == cities["Tallinn"])

# Flight constraints: transitions between consecutive days must be valid flights or same city
for i in range(days - 1):
    current_day = day_vars[i]
    next_day = day_vars[i + 1]
    solver.add(Or(
        current_day == next_day,  # stay in the same city
        # or there's a direct flight
        Or([And(current_day == from_city, next_day == to_city) 
            for from_city in direct_flights 
            for to_city in direct_flights[from_city]])
    ))

# Check if the solver can find a solution
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