import json
from z3 import *

def solve_itinerary():
    # Define cities with numerical codes
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
    
    # Required days in each city (including travel days)
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
    
    num_days = 23
    day = [Int(f"day_{i}") for i in range(num_days)]
    s = Solver()

    # Each day must be one of the cities
    for d in day:
        s.add(Or([d == city for city in cities.values()]))

    # Flight constraints - must be direct flights or same city
    for i in range(num_days - 1):
        current = day[i]
        next_day = day[i + 1]
        # Create all possible flight options
        flight_options = []
        for src in direct_flights:
            for dest in direct_flights[src]:
                flight_options.append(And(current == src, next_day == dest))
        s.add(Or(current == next_day, Or(flight_options)))

    # Count days in each city (including travel days)
    for city in cities.values():
        count = Sum([If(day[i] == city, 1, 0) for i in range(num_days)])
        s.add(count == required_days[city])

    # Workshop in Bucharest must include days 16-19 (1-based)
    # So days 15-18 in 0-based
    s.add(day[15] == cities["Bucharest"])
    s.add(day[16] == cities["Bucharest"])
    s.add(day[17] == cities["Bucharest"])
    s.add(day[18] == cities["Bucharest"])

    # Show in Istanbul on days 12-13 (1-based)
    # So days 11-12 in 0-based
    s.add(day[11] == cities["Istanbul"])
    s.add(day[12] == cities["Istanbul"])

    # Ensure we don't have impossible single-day visits
    for i in range(1, num_days - 1):
        s.add(Or(
            day[i] == day[i-1],
            day[i] == day[i+1],
            And(day[i-1] == day[i+1], day[i] != day[i-1])
        ))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_days):
            city_code = model[day[i]].as_long()
            city_name = city_names[city_code]
            itinerary.append({"day": i + 1, "place": city_name})
        
        return json.dumps({"itinerary": itinerary}, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

print(solve_itinerary())