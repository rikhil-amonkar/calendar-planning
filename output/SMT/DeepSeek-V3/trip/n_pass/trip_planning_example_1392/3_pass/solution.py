import json
from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", "Amsterdam", "Nice", "Barcelona", "Porto"]
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as adjacency list
    direct_flights = {
        "Venice": ["Nice", "Amsterdam", "Stuttgart", "Naples", "Barcelona"],
        "Naples": ["Amsterdam", "Split", "Nice", "Valencia", "Barcelona", "Venice", "Stuttgart", "Porto"],
        "Barcelona": ["Nice", "Porto", "Valencia", "Naples", "Venice", "Amsterdam", "Stuttgart", "Split"],
        "Amsterdam": ["Naples", "Nice", "Valencia", "Venice", "Barcelona", "Stuttgart", "Porto", "Split"],
        "Stuttgart": ["Valencia", "Porto", "Split", "Naples", "Venice", "Barcelona", "Amsterdam"],
        "Split": ["Stuttgart", "Naples", "Barcelona", "Amsterdam"],
        "Valencia": ["Stuttgart", "Amsterdam", "Naples", "Barcelona", "Porto"],
        "Nice": ["Venice", "Barcelona", "Amsterdam", "Naples", "Porto"],
        "Porto": ["Stuttgart", "Barcelona", "Nice", "Amsterdam", "Valencia", "Naples"]
    }
    
    # Precompute allowed transitions (city1, city2) where there's a direct flight
    allowed_transitions = set()
    for city1 in direct_flights:
        for city2 in direct_flights[city1]:
            allowed_transitions.add((city_map[city1], city_map[city2]))
    
    # Total days
    total_days = 24
    
    # Create Z3 variables: assign a city to each day
    day_to_city = [Int(f"day_{day}") for day in range(total_days)]
    
    # Create solver
    solver = Solver()
    
    # Each day's assignment must be a valid city index (0 to 8)
    for day in range(total_days):
        solver.add(day_to_city[day] >= 0, day_to_city[day] < len(cities))
    
    # Duration constraints
    # Naples: 3 days
    solver.add(Sum([If(day_to_city[day] == city_map["Naples"], 1, 0) for day in range(total_days)]) == 3)
    # Valencia: 5 days
    solver.add(Sum([If(day_to_city[day] == city_map["Valencia"], 1, 0) for day in range(total_days)]) == 5)
    # Stuttgart: 2 days
    solver.add(Sum([If(day_to_city[day] == city_map["Stuttgart"], 1, 0) for day in range(total_days)]) == 2)
    # Split: 5 days
    solver.add(Sum([If(day_to_city[day] == city_map["Split"], 1, 0) for day in range(total_days)]) == 5)
    # Venice: 5 days
    solver.add(Sum([If(day_to_city[day] == city_map["Venice"], 1, 0) for day in range(total_days)]) == 5)
    # Amsterdam: 4 days
    solver.add(Sum([If(day_to_city[day] == city_map["Amsterdam"], 1, 0) for day in range(total_days)]) == 4)
    # Nice: 2 days
    solver.add(Sum([If(day_to_city[day] == city_map["Nice"], 1, 0) for day in range(total_days)]) == 2)
    # Barcelona: 2 days
    solver.add(Sum([If(day_to_city[day] == city_map["Barcelona"], 1, 0) for day in range(total_days)]) == 2)
    # Porto: 4 days
    solver.add(Sum([If(day_to_city[day] == city_map["Porto"], 1, 0) for day in range(total_days)]) == 4)
    
    # Specific day constraints
    # Conference in Venice between day 6 and 10 (inclusive). So at least one day in Venice in 5-9 (0-based).
    solver.add(Or([day_to_city[day] == city_map["Venice"] for day in range(5, 10)]))
    # Workshop in Barcelona between day 5 and 6. So Barcelona must be on day 4 or 5 (0-based).
    solver.add(Or(day_to_city[4] == city_map["Barcelona"], day_to_city[5] == city_map["Barcelona"]))
    # Meet friend in Naples between day 18 and 20 (inclusive). So Naples must be on day 17, 18, or 19 (0-based).
    solver.add(Or([day_to_city[day] == city_map["Naples"] for day in range(17, 20)]))
    # Meet friends in Nice between day 23 and 24 (inclusive). So Nice must be on day 22 or 23 (0-based).
    solver.add(Or(day_to_city[22] == city_map["Nice"], day_to_city[23] == city_map["Nice"]))
    
    # Flight constraints: consecutive days must be either the same city or connected by direct flights
    for day in range(total_days - 1):
        current_city = day_to_city[day]
        next_city = day_to_city[day + 1]
        # Either stay in the same city or move to a directly connected city
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == c1, next_city == c2) for (c1, c2) in allowed_transitions]
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(total_days):
            city_idx = model.evaluate(day_to_city[day]).as_long()
            itinerary.append({"day": day + 1, "city": cities[city_idx]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))