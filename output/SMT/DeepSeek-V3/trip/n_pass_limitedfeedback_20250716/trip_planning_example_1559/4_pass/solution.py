import json
from z3 import *

def solve_itinerary():
    # Define cities and required days
    cities = {
        "Valencia": 2,
        "Oslo": 3,
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": 5,
        "Tallinn": 2,
        "Mykonos": 5,
        "Lisbon": 2
    }

    # Define direct flights (bidirectional)
    direct_flights = [
        ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"),
        ("Prague", "Lyon"), ("Paris", "Oslo"), ("Lisbon", "Seville"),
        ("Prague", "Lisbon"), ("Oslo", "Nice"), ("Valencia", "Paris"),
        ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
        ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"),
        ("Prague", "Paris"), ("Seville", "Paris"), ("Oslo", "Lyon"),
        ("Prague", "Valencia"), ("Lisbon", "Nice"), ("Lisbon", "Oslo"),
        ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
        ("Prague", "Tallinn")
    ]

    # Create bidirectional flight connections
    flight_connections = {}
    for city in cities:
        flight_connections[city] = set()
    for a, b in direct_flights:
        flight_connections[a].add(b)
        flight_connections[b].add(a)

    # Initialize solver with better parameters
    solver = Solver()
    solver.set("timeout", 30000)  # 30 second timeout

    # Create day variables (1-25)
    days = [Int(f"day_{i}") for i in range(1, 26)]
    city_names = {city: idx for idx, city in enumerate(cities.keys())}
    city_indices = {idx: city for idx, city in enumerate(cities.keys())}

    # Basic constraints: each day must be a valid city
    for day in days:
        solver.add(day >= 0, day < len(cities))

    # Total days per city must match requirements
    for city, req_days in cities.items():
        solver.add(Sum([If(day == city_names[city], 1, 0) for day in days]) == req_days)

    # Event constraints
    # Valencia: 2 days, including day 3 or 4
    solver.add(Or(days[2] == city_names["Valencia"], days[3] == city_names["Valencia"]))
    
    # Oslo: 3 days, including day 13-15
    solver.add(Or([days[i] == city_names["Oslo"] for i in range(12, 15)]))
    
    # Seville: days 5-9 (inclusive)
    for i in range(4, 9):
        solver.add(days[i] == city_names["Seville"])
    
    # Mykonos: days 21-25 (inclusive)
    for i in range(20, 25):
        solver.add(days[i] == city_names["Mykonos"])

    # Flight constraints with better handling of transitions
    for i in range(24):
        current = days[i]
        next_c = days[i+1]
        
        # Either stay in same city or use a direct flight
        same_city = current == next_c
        possible_flights = []
        for city in cities:
            for neighbor in flight_connections[city]:
                possible_flights.append(And(current == city_names[city], next_c == city_names[neighbor]))
        
        solver.add(Or(same_city, Or(possible_flights)))

    # Add helper constraints to guide the solver
    # Ensure we don't have too many consecutive same-city days
    for i in range(22):
        solver.add(Not(And([days[j] == days[j+1] for j in range(i, i+3)])))

    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 26):
            city_idx = model.evaluate(days[i-1]).as_long()
            city = city_indices[city_idx]
            itinerary.append({"day": i, "place": city})
        return {"itinerary": itinerary}
    else:
        print("Failed to find solution. Reasons:")
        print(solver.reason_unknown())
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found after optimization attempts.")