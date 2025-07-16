import json
from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", "Amsterdam", "Nice", "Barcelona", "Porto"]
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as adjacency matrix
    flight_matrix = [
        [0, 1, 1, 1, 1, 1, 1, 1, 1],  # Naples
        [1, 0, 1, 0, 0, 1, 0, 1, 1],  # Valencia
        [1, 1, 0, 1, 1, 1, 0, 1, 1],  # Stuttgart
        [1, 0, 1, 0, 0, 1, 0, 1, 0],  # Split
        [1, 0, 1, 0, 0, 1, 1, 1, 0],  # Venice
        [1, 1, 1, 1, 1, 0, 1, 1, 1],  # Amsterdam
        [1, 0, 0, 0, 1, 1, 0, 1, 1],  # Nice
        [1, 1, 1, 1, 1, 1, 1, 0, 1],  # Barcelona
        [1, 1, 1, 0, 0, 1, 1, 1, 0]   # Porto
    ]
    
    # Total days
    total_days = 24
    
    # Create Z3 variables
    day_to_city = [Int(f"day_{day}") for day in range(total_days)]
    
    # Create solver with timeout
    solver = Solver()
    solver.set("timeout", 30000)  # 30 second timeout
    
    # City assignments must be valid
    for day in range(total_days):
        solver.add(day_to_city[day] >= 0, day_to_city[day] < len(cities))
    
    # Duration constraints
    for city, days in [("Naples", 3), ("Valencia", 5), ("Stuttgart", 2),
                      ("Split", 5), ("Venice", 5), ("Amsterdam", 4),
                      ("Nice", 2), ("Barcelona", 2), ("Porto", 4)]:
        solver.add(Sum([If(day_to_city[day] == city_map[city], 1, 0) 
                   for day in range(total_days)) == days)
    
    # Specific day constraints
    # Conference in Venice days 6-10 (0-based 5-9)
    solver.add(Or([day_to_city[day] == city_map["Venice"] for day in range(5, 10)]))
    # Workshop in Barcelona days 5-6 (0-based 4-5)
    solver.add(Or(day_to_city[4] == city_map["Barcelona"], day_to_city[5] == city_map["Barcelona"]))
    # Meet in Naples days 18-20 (0-based 17-19)
    solver.add(Or([day_to_city[day] == city_map["Naples"] for day in range(17, 20)]))
    # Meet in Nice days 23-24 (0-based 22-23)
    solver.add(Or(day_to_city[22] == city_map["Nice"], day_to_city[23] == city_map["Nice"]))
    
    # Flight constraints using adjacency matrix
    for day in range(total_days - 1):
        current = day_to_city[day]
        next_c = day_to_city[day + 1]
        solver.add(Or(
            current == next_c,
            *[And(current == i, next_c == j) 
              for i in range(len(cities)) 
              for j in range(len(cities)) 
              if flight_matrix[i][j]]
        ))
    
    # Symmetry breaking: Start in Naples (arbitrary choice)
    solver.add(day_to_city[0] == city_map["Naples"])
    
    # Try to solve
    result = solver.check()
    if result == sat:
        model = solver.model()
        itinerary = []
        for day in range(total_days):
            city_idx = model.evaluate(day_to_city[day]).as_long()
            itinerary.append({"day": day + 1, "city": cities[city_idx]})
        return {"itinerary": itinerary}
    elif result == unknown:
        return {"error": "Timeout reached, no solution found"}
    else:
        return {"error": "No valid itinerary exists"}

# Solve and print
result = solve_itinerary()
print(json.dumps(result, indent=2))