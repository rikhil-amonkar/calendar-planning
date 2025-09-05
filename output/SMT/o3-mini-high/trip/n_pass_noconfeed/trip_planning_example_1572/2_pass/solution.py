from z3 import *
import json

# Define indices for cities and their durations
# 0: Lyon (3 days)
# 1: Paris (5 days)
# 2: Riga (2 days)
# 3: Berlin (2 days)
# 4: Stockholm (3 days)
# 5: Zurich (5 days)
# 6: Nice (2 days)
# 7: Seville (3 days)
# 8: Milan (3 days)
# 9: Naples (4 days)
cities = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", 
          "Zurich", "Nice", "Seville", "Milan", "Naples"]
durations = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]

# Allowed direct flights (neighbors) for each city (using indices)
allowed_neighbors = {
    0: [1, 6],             
    1: [0, 2, 3, 4, 5, 6, 7, 8, 9],  
    2: [1, 3, 4, 5, 6, 8],  
    3: [1, 2, 4, 6, 8, 9],  
    4: [1, 2, 3, 5, 6, 8],  
    5: [1, 2, 4, 6, 8, 9],  
    6: [0, 1, 2, 3, 4, 5, 9],  
    7: [1],                
    8: [1, 2, 3, 4, 5, 9],  
    9: [1, 3, 5, 6, 8]     
}

# Create the solver instance
solver = Solver()

# Create variables:
# order[i] represents the city index visited in position i
order = [Int(f"order_{i}") for i in range(10)]
# T[i] represents the starting day for the segment corresponding to the city at position i.
T = [Int(f"T_{i}") for i in range(10)]

# Domain constraints for order (each city index must be between 0 and 9)
for i in range(10):
    solver.add(order[i] >= 0, order[i] < 10)
# All cities must be visited exactly once.
solver.add(Distinct(order))

# Helper function to obtain the duration of a city using a list comprehension.
def get_duration(city_expr):
    return Sum([If(city_expr == i, durations[i], 0) for i in range(len(durations))])

# The trip lasts exactly 23 days.
solver.add(T[0] == 1)
for i in range(9):
    solver.add(T[i+1] == T[i] + (get_duration(order[i]) - 1))
# The last city's end day must equal 23.
solver.add(T[9] + get_duration(order[9]) - 1 == 23)

# Special event constraints:
for i in range(10):
    solver.add(Implies(order[i] == 3, T[i] <= 2))
for i in range(10):
    solver.add(Implies(order[i] == 4, T[i] == 20))
for i in range(10):
    solver.add(Implies(order[i] == 6, Or(T[i] == 11, T[i] == 12, T[i] == 13)))

# Flight connectivity constraints: consecutive cities must have a direct flight.
for i in range(9):
    constraints = []
    for city in range(10):
        neighbors = allowed_neighbors.get(city, [])
        neighbor_cond = Or([order[i+1] == nb for nb in neighbors])
        constraints.append(Implies(order[i] == city, neighbor_cond))
    solver.add(And(constraints))

# Check and print a solution if it exists
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(10):
        city_index = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(T[i]).as_long()
        duration_val = durations[city_index]
        end_day = start_day + duration_val - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_index]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))