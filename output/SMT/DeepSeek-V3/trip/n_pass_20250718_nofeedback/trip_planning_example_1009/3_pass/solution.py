from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        "Bucharest": ["Vienna", "Riga", "Istanbul", "Manchester"],
        "Vienna": ["Bucharest", "Reykjavik", "Manchester", "Riga", "Istanbul", "Florence", "Stuttgart"],
        "Reykjavik": ["Vienna", "Stuttgart"],
        "Manchester": ["Vienna", "Riga", "Istanbul", "Bucharest", "Stuttgart"],
        "Riga": ["Vienna", "Manchester", "Bucharest", "Istanbul"],
        "Istanbul": ["Vienna", "Riga", "Stuttgart", "Bucharest", "Manchester"],
        "Florence": ["Vienna"],
        "Stuttgart": ["Vienna", "Istanbul", "Reykjavik", "Manchester"]
    }
    
    # Total days
    total_days = 23
    
    # Create Z3 variables for each day's location
    days = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Create a solver instance
    solver = Solver()
    
    # Assign each day's variable to a city (encoded as integers)
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day's value must be a valid city id
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Constraint: transitions between cities must be via direct flights
    for i in range(total_days - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # Either stay in the same city or move to a directly connected city
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[city], next_city == city_ids[neighbor])
              for city in direct_flights
              for neighbor in direct_flights[city]]
        ))
    
    # Constraint: each city must be visited for exactly the required days
    for city, required_days in cities.items():
        city_id = city_ids[city]
        solver.add(Sum([If(day == city_id, 1, 0) for day in days]) == required_days)
    
    # Constraint: workshop in Bucharest between day 16 and 19 (inclusive)
    solver.add(Or(*[days[i] == city_ids["Bucharest"] for i in range(15, 19)]))  # days are 1-based, so 16-19 is 15-18 in 0-based
    
    # Constraint: show in Istanbul on day 12 and 13
    solver.add(days[11] == city_ids["Istanbul"])  # day 12 is index 11
    solver.add(days[12] == city_ids["Istanbul"])  # day 13 is index 12
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(total_days):
            city_id = model.evaluate(days[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i + 1, "place": city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))