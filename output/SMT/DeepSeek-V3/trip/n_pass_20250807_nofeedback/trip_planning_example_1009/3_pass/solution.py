import json
from z3 import *

def solve_itinerary():
    # Define the cities and their codes
    cities = {
        "Riga": 0,
        "Manchester": 1,
        "Bucharest": 2,
        "Florence": 3,
        "Vienna": 4,
        "Istanbul": 5,
        "Reykjavik": 6,
        "Stuttgart": 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights as adjacency list
    direct_flights = {
        0: [1, 2, 4, 5],  # Riga
        1: [0, 2, 4, 5, 7],  # Manchester
        2: [0, 1, 4, 5],  # Bucharest
        3: [4],  # Florence
        4: [0, 1, 2, 3, 5, 6, 7],  # Vienna
        5: [0, 1, 2, 4, 7],  # Istanbul
        6: [4, 7],  # Reykjavik
        7: [1, 4, 5, 6]  # Stuttgart
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Riga
        1: 5,  # Manchester
        2: 4,  # Bucharest
        3: 4,  # Florence
        4: 2,  # Vienna
        5: 2,  # Istanbul
        6: 4,  # Reykjavik
        7: 5   # Stuttgart
    }
    
    # Create Z3 variables: day[i] represents the city on day i+1 (days are 1-based)
    num_days = 23
    day = [Int(f"day_{i}") for i in range(num_days)]
    
    s = Solver()
    
    # Each day must be one of the cities
    for d in day:
        s.add(Or([d == city for city in cities.values()]))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Create a disjunction for all possible direct flights from current_city
        flight_options = []
        for city_code in cities.values():
            for adj in direct_flights[city_code]:
                flight_options.append(And(current_city == city_code, next_city == adj))
        s.add(Or(current_city == next_city, Or(flight_options)))
    
    # Count days per city
    for city in cities.values():
        count = Sum([If(day[i] == city, 1, 0) for i in range(num_days)])
        s.add(count == required_days[city])
    
    # Workshop in Bucharest between day 16 and 19 (inclusive, 1-based)
    # So days 15 to 18 in 0-based
    s.add(Or([day[i] == cities["Bucharest"] for i in range(15, 19)]))
    
    # Show in Istanbul on day 12 and 13 (1-based: days 11 and 12 in 0-based)
    s.add(day[11] == cities["Istanbul"])
    s.add(day[12] == cities["Istanbul"])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_days):
            city_code = model[day[i]].as_long()
            city_name = city_names[city_code]
            itinerary.append({"day": i + 1, "place": city_name})
        
        result = {"itinerary": itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

# Execute the solver and print the result
print(solve_itinerary())