import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = [
        "Venice",
        "Reykjavik",
        "Munich",
        "Santorini",
        "Manchester",
        "Porto",
        "Bucharest",
        "Tallinn",
        "Valencia",
        "Vienna"
    ]
    
    # Direct flights as per the problem description
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Tallinn", "Valencia"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Bucharest", "Santorini", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Porto": ["Munich", "Vienna", "Manchester", "Valencia"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Venice", "Porto", "Munich"],
        "Valencia": ["Vienna", "Bucharest", "Porto", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }
    
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
        ("Munich", 4, 6),  # Munich from day 4 to 6
        ("Santorini", 8, 10),  # Santorini between day 8 and 10
        ("Valencia", 14, 15)   # Valencia on day 14 and 15
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city visited on day i (1-based)
    days = [Int(f"day_{i}") for i in range(1, 25)]
    
    # Each day variable must be between 0 and 9 (index of cities)
    for d in days:
        s.add(And(d >= 0, d <= 9))
    
    # Helper function to get city index
    def city_index(city):
        return cities.index(city)
    
    # Fixed events constraints
    for city, start, end in fixed_events:
        idx = city_index(city)
        for day in range(start, end + 1):
            s.add(days[day - 1] == idx)
    
    # Duration constraints: each city must appear required_days times
    for city, req in required_days.items():
        idx = city_index(city)
        s.add(Sum([If(d == idx, 1, 0) for d in days]) == req)
    
    # Flight transitions: consecutive days must be same city or have a direct flight
    for i in range(24 - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_index(a), next_city == city_index(b))
              for a in cities for b in direct_flights.get(a, [])]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 25):
            city_idx = m.evaluate(days[i - 1]).as_long()
            itinerary.append({"day": i, "place": cities[city_idx]})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured this)
        # Convert to JSON
        result = {"itinerary": itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

# Execute the solver and print the result
print(solve_itinerary())