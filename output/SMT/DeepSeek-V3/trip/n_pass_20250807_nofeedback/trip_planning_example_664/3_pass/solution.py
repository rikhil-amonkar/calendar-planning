from z3 import *

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan")
    ]
    
    # Build adjacency list for direct flights
    adjacency = {}
    for city in cities:
        adjacency[city] = []
    
    for from_city, to_city in direct_flights:
        if to_city not in adjacency[from_city]:
            adjacency[from_city].append(to_city)
        if from_city not in adjacency[to_city]:
            adjacency[to_city].append(from_city)
    
    # Total days
    total_days = 18
    
    # Create Z3 solver
    solver = Solver()
    
    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {v: k for k, v in city_ids.items()}
    
    # Create variables for each day's city
    day_to_city = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Constraint: each day's city must be one of the six cities
    for day in day_to_city:
        solver.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraint: total days per city must match requirements
    for city, days in cities.items():
        solver.add(Sum([If(day == city_ids[city], 1, 0) for day in day_to_city]) == days)
    
    # Constraint: transitions must be via direct flights
    for i in range(total_days - 1):
        current_city = day_to_city[i]
        next_city = day_to_city[i + 1]
        solver.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_ids[city_from], next_city == city_ids[city_to])
                for city_from in adjacency
                for city_to in adjacency[city_from]
            ]
        ))
    
    # Time window constraints
    # Bucharest between day 1 and 4
    solver.add(Or([day_to_city[i] == city_ids["Bucharest"] for i in range(4)]))
    # Munich between day 4 and 8
    solver.add(Or([day_to_city[i] == city_ids["Munich"] for i in range(3, 8)]))
    # Seville between day 8 and 12
    solver.add(Or([day_to_city[i] == city_ids["Seville"] for i in range(7, 12)]))
    
    # Ensure contiguous stays for each city
    for city in cities:
        # Create a list indicating whether the city is visited on each day
        is_city = [day_to_city[i] == city_ids[city] for i in range(total_days)]
        # The sum of transitions (0 to 1 or 1 to 0) must be <= 2 for a contiguous block
        transitions = []
        for i in range(total_days - 1):
            transitions.append(If(is_city[i] != is_city[i + 1], 1, 0))
        solver.add(Sum(transitions) <= 2)
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(total_days):
            city_id = model.evaluate(day_to_city[i]).as_long()
            itinerary.append({"day": i + 1, "place": id_to_city[city_id]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))