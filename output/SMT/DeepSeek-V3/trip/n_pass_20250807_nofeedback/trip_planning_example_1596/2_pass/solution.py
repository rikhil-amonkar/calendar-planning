import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Budapest", "Munich"),
        ("Bucharest", "Riga"),
        ("Munich", "Krakow"),
        ("Munich", "Warsaw"),
        ("Munich", "Bucharest"),
        ("Edinburgh", "Stockholm"),
        ("Barcelona", "Warsaw"),
        ("Edinburgh", "Krakow"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Krakow"),
        ("Budapest", "Vienna"),
        ("Barcelona", "Stockholm"),
        ("Stockholm", "Munich"),
        ("Edinburgh", "Budapest"),
        ("Barcelona", "Riga"),
        ("Edinburgh", "Barcelona"),
        ("Vienna", "Riga"),
        ("Barcelona", "Budapest"),
        ("Bucharest", "Warsaw"),
        ("Vienna", "Krakow"),
        ("Edinburgh", "Munich"),
        ("Barcelona", "Bucharest"),
        ("Edinburgh", "Riga"),
        ("Vienna", "Stockholm"),
        ("Warsaw", "Krakow"),
        ("Barcelona", "Krakow"),
        ("Riga", "Munich"),
        ("Vienna", "Bucharest"),
        ("Budapest", "Warsaw"),
        ("Vienna", "Warsaw"),
        ("Barcelona", "Vienna"),
        ("Budapest", "Bucharest"),
        ("Vienna", "Munich"),
        ("Riga", "Warsaw"),
        ("Stockholm", "Riga"),
        ("Stockholm", "Warsaw")
    ]
    
    # Create graph adjacency list
    graph = {city: [] for city in cities}
    for a, b in direct_flights:
        if a in cities and b in cities:
            graph[a].append(b)
            graph[b].append(a)
    
    # Z3 solver setup
    s = Solver()
    
    # Day variables: day[i] is the city on day i+1 (0-based)
    days = 32
    day_vars = [Int(f"day_{i}") for i in range(days)]
    
    # City to integer mapping
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}
    
    # Each day must be one of the cities
    for day in day_vars:
        s.add(Or([day == city_to_int[city] for city in cities]))
    
    # Consecutive days must be same city or connected by a flight
    for i in range(days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,
            Or([And(current == city_to_int[a], next_day == city_to_int[b]) 
                for a in cities for b in graph[a]])
        ))
    
    # Total days per city
    for city in cities:
        total = Sum([If(day_vars[i] == city_to_int[city], 1, 0) for i in range(days)])
        s.add(total == cities[city])
    
    # Event constraints:
    # Munich workshop between day 18-20 (1-based: days 17-19 0-based)
    s.add(Or([day_vars[i] == city_to_int["Munich"] for i in range(17, 20)]))
    
    # Warsaw conference between day 25-29 (1-based: days 24-28 0-based)
    for i in range(24, 29):
        s.add(day_vars[i] == city_to_int["Warsaw"])
    
    # Budapest show between day 9-13 (1-based: days 8-12 0-based)
    for i in range(8, 13):
        s.add(day_vars[i] == city_to_int["Budapest"])
    
    # Stockholm friends between day 17-18 (1-based: days 16-17 0-based)
    s.add(Or([day_vars[i] == city_to_int["Stockholm"] for i in range(16, 18)]))
    
    # Edinburgh friend between day 1-5 (1-based: days 0-4 0-based)
    s.add(Or([day_vars[i] == city_to_int["Edinburgh"] for i in range(0, 5)]))
    
    # Check for a solution with a timeout
    s.set("timeout", 60000)  # 60 seconds timeout
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": i + 1, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found within the time limit"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))