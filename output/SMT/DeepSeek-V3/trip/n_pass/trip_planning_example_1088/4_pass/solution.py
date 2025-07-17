import json
from z3 import *

def solve_itinerary():
    # Define cities and required days
    cities = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3
    }

    # Define bidirectional flight connections
    flight_connections = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva", "Reykjavik"],
        "Stuttgart": ["Porto", "Stockholm", "Split", "Reykjavik"],
        "Oslo": ["Split", "Geneva", "Porto", "Stockholm", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Geneva", "Stockholm", "Oslo"],
        "Geneva": ["Porto", "Split", "Stockholm", "Oslo"],
        "Porto": ["Stuttgart", "Geneva", "Oslo"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }

    # Initialize Z3 solver
    solver = Solver()

    # Create day variables (1-21)
    days = 21
    day_vars = [Int(f"day_{i}") for i in range(1, days+1)]

    # City encodings
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}

    # Constrain each day to be a valid city
    for day in day_vars:
        solver.add(Or([day == city_ids[city] for city in cities]))

    # Fixed constraints
    # Days 1-2 in Reykjavik
    solver.add(day_vars[0] == city_ids["Reykjavik"])
    solver.add(day_vars[1] == city_ids["Reykjavik"])

    # Days 19-21 in Porto
    solver.add(day_vars[18] == city_ids["Porto"])
    solver.add(day_vars[19] == city_ids["Porto"])
    solver.add(day_vars[20] == city_ids["Porto"])

    # Stockholm between days 2-4
    solver.add(Or([day_vars[i] == city_ids["Stockholm"] for i in [1, 2, 3]]))

    # Flight transitions
    for i in range(days-1):
        current = day_vars[i]
        next_day = day_vars[i+1]
        # If cities are different, must have flight connection
        solver.add(Implies(current != next_day,
                         Or([And(current == city_ids[src], next_day == city_ids[dst])
                            for src in flight_connections 
                            for dst in flight_connections[src]])))

    # Duration constraints
    for city in cities:
        count = Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(days)])
        solver.add(count == cities[city])

    # Solve
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            city_id = model.evaluate(day_vars[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify all cities are visited
        visited = set([entry["place"] for entry in itinerary])
        if len(visited) == len(cities):
            return {"itinerary": itinerary}
        else:
            print("Not all cities were visited")
            return None
    else:
        print("No solution found")
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("Failed to find a valid itinerary")