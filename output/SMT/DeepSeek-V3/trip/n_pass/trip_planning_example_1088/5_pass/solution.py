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

    # Stockholm between days 2-4 (indices 1-3)
    solver.add(Or([day_vars[i] == city_ids["Stockholm"] for i in [1, 2, 3]]))

    # Flight transitions - must have direct connection when changing cities
    for i in range(days-1):
        current = day_vars[i]
        next_day = day_vars[i+1]
        solver.add(Implies(current != next_day,
                         Or([And(current == city_ids[src], next_day == city_ids[dst])
                            for src in flight_connections 
                            for dst in flight_connections[src]])))

    # Duration constraints - count days in each city
    for city in cities:
        count = Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(days)])
        solver.add(count == cities[city])

    # Solve with a timeout
    solver.set("timeout", 60000)  # 60 second timeout
    result = solver.check()
    
    if result == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            city_id = model.evaluate(day_vars[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify all constraints are met
        if verify_itinerary(itinerary, cities, flight_connections):
            return {"itinerary": itinerary}
        else:
            print("Generated itinerary failed verification")
            return None
    else:
        print("No solution found")
        print(solver.reason_unknown())
        return None

def verify_itinerary(itinerary, cities, flight_connections):
    # Verify all cities are visited with correct durations
    city_days = {city: 0 for city in cities}
    for day in itinerary:
        city_days[day["place"]] += 1
    
    for city, required in cities.items():
        if city_days[city] != required:
            print(f"City {city} has {city_days[city]} days instead of {required}")
            return False

    # Verify flight connections
    for i in range(len(itinerary)-1):
        current = itinerary[i]["place"]
        next_city = itinerary[i+1]["place"]
        if current != next_city and next_city not in flight_connections.get(current, []):
            print(f"Invalid flight from {current} to {next_city}")
            return False

    # Verify fixed days
    if itinerary[0]["place"] != "Reykjavik" or itinerary[1]["place"] != "Reykjavik":
        print("Days 1-2 must be in Reykjavik")
        return False
    
    if not any(itinerary[i]["place"] == "Stockholm" for i in [1,2,3]):
        print("Stockholm must appear between days 2-4")
        return False
    
    if not all(itinerary[i]["place"] == "Porto" for i in [18,19,20]):
        print("Days 19-21 must be in Porto")
        return False

    return True

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("Failed to find a valid itinerary")