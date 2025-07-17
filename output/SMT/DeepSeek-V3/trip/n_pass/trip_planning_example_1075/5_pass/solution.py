import json
from z3 import *

def solve_itinerary():
    # Define cities and required days
    cities = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }

    # Direct flight connections (bidirectional)
    flight_connections = [
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Vienna"),
        ("Reykjavik", "Prague"),
        ("Stuttgart", "Split"),
        ("Stuttgart", "Vienna"),
        ("Stuttgart", "Edinburgh"),
        ("Stuttgart", "Manchester"),
        ("Prague", "Manchester"),
        ("Prague", "Edinburgh"),
        ("Prague", "Vienna"),
        ("Prague", "Split"),
        ("Prague", "Lyon"),
        ("Manchester", "Split"),
        ("Manchester", "Vienna"),
        ("Edinburgh", "Prague"),
        ("Edinburgh", "Stuttgart"),
        ("Vienna", "Lyon"),
        ("Vienna", "Split"),
        ("Vienna", "Reykjavik"),
        ("Split", "Lyon"),
        ("Lyon", "Prague")
    ]

    # Initialize Z3 solver
    s = Solver()

    # Create city enumeration
    City = Datatype('City')
    for city in cities.keys():
        City.declare(city)
    City = City.create()
    city_consts = {city: getattr(City, city) for city in cities.keys()}

    # Create flight relation
    Flight = Function('Flight', City, City, BoolSort())
    for src, dest in flight_connections:
        s.add(Flight(city_consts[src], city_consts[dest]))
        s.add(Flight(city_consts[dest], city_consts[src]))

    # Variables for each day (1-25)
    location = [Const(f'day_{i}', City) for i in range(1, 26)]
    is_travel_day = [Bool(f'travel_{i}') for i in range(1, 26)]

    # Constraints for travel days
    for i in range(25):
        # If it's a travel day, next location must be reachable by flight
        if i < 24:
            s.add(Implies(is_travel_day[i], 
                         Flight(location[i], location[i+1])))

    # Count days in each city
    for city, days in cities.items():
        count = 0
        for i in range(25):
            count += If(location[i] == city_consts[city], 1, 0)
        s.add(count == days)

    # Fixed events constraints
    # Edinburgh must be visited from day 5-8 (inclusive)
    for day in range(4, 8):  # 0-based days 4-7 (1-based 5-8)
        s.add(location[day] == city_consts["Edinburgh"])

    # Split must include days 19-23 (wedding)
    wedding_days = []
    for day in range(18, 23):  # 0-based days 18-22 (1-based 19-23)
        wedding_days.append(location[day] == city_consts["Split"])
    s.add(Or(*wedding_days))

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, 26):
            city = str(m.evaluate(location[day-1]))
            if city != current_city:
                if current_city is not None:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{day-1}",
                        "place": current_city
                    })
                current_city = city
                start_day = day
        
        # Add the last segment
        itinerary.append({
            "day_range": f"Day {start_day}-25",
            "place": current_city
        })

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))