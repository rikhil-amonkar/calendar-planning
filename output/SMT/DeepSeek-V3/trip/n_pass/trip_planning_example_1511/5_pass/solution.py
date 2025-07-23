import json
from z3 import *

def solve_itinerary():
    # Cities with their indices
    cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", 
              "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Bucharest", "Manchester"),
        ("Bucharest", "Valencia"),
        ("Bucharest", "Vienna"),
        ("Bucharest", "Munich"),
        ("Bucharest", "Santorini"),
        ("Munich", "Venice"),
        ("Munich", "Porto"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Munich", "Vienna"),
        ("Munich", "Tallinn"),
        ("Munich", "Valencia"),
        ("Santorini", "Manchester"),
        ("Santorini", "Venice"),
        ("Santorini", "Vienna"),
        ("Vienna", "Reykjavik"),
        ("Vienna", "Valencia"),
        ("Vienna", "Manchester"),
        ("Vienna", "Porto"),
        ("Vienna", "Venice"),
        ("Venice", "Manchester"),
        ("Porto", "Manchester"),
        ("Porto", "Valencia"),
        ("Valencia", "Manchester"),
        ("Reykjavik", "Munich"),
        ("Tallinn", "Munich")
    ]
    
    # Create flight connections (both directions)
    flight_connections = {}
    for city in cities:
        flight_connections[city] = set()
    
    for a, b in direct_flights:
        flight_connections[a].add(b)
        flight_connections[b].add(a)
    
    # Required days per city
    required_days = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Fixed events
    fixed_events = [
        ("Munich", 4, 6),    # Munich from day 4 to 6
        ("Santorini", 8, 10), # Santorini from day 8 to 10
        ("Valencia", 14, 15)  # Valencia on day 14 and 15
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city visited on day i (1-based)
    days = [Int(f"day_{i}") for i in range(1, 25)]
    
    # Each day variable must be a valid city index
    for d in days:
        s.add(And(d >= 0, d < len(cities)))
    
    # Fixed events constraints
    for city, start, end in fixed_events:
        idx = city_index[city]
        for day in range(start, end + 1):
            s.add(days[day - 1] == idx)
    
    # Duration constraints
    for city, req in required_days.items():
        idx = city_index[city]
        s.add(Sum([If(d == idx, 1, 0) for d in days]) == req)
    
    # Flight transition constraints
    for i in range(23):  # For days 1-23 (since we look at day i+1)
        current = days[i]
        next_day = days[i + 1]
        
        # Either stay in same city or move to connected city
        same_city = current == next_day
        possible_transitions = []
        
        for city in cities:
            connected_cities = flight_connections[city]
            for connected in connected_cities:
                possible_transitions.append(
                    And(current == city_index[city], 
                        next_day == city_index[connected])
                )
        
        s.add(Or(same_city, *possible_transitions))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 25):
            city_idx = m.evaluate(days[i - 1]).as_long()
            itinerary.append({"day": i, "place": cities[city_idx]})
        
        # Verify all constraints are met
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry["place"]] += 1
        
        for city, req in required_days.items():
            assert city_counts[city] == req, f"City {city} count mismatch"
        
        # Verify fixed events
        for city, start, end in fixed_events:
            for day in range(start, end + 1):
                assert itinerary[day - 1]["place"] == city, f"Fixed event mismatch on day {day}"
        
        # Verify flight connections
        for i in range(23):
            current = itinerary[i]["place"]
            next_city = itinerary[i + 1]["place"]
            if current != next_city:
                assert next_city in flight_connections[current], f"Invalid flight from {current} to {next_city}"
        
        return json.dumps({"itinerary": itinerary}, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

print(solve_itinerary())