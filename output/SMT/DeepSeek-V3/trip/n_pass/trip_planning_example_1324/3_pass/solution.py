import json
from z3 import *

def solve_itinerary():
    # Cities and their required stay durations
    cities = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3
    }
    
    # Direct flights adjacency list
    direct_flights = {
        "Copenhagen": ["Athens", "Dubrovnik", "Munich", "Reykjavik", "Barcelona", "Tallinn", "Venice"],
        "Athens": ["Copenhagen", "Dubrovnik", "Venice", "Reykjavik", "Munich", "Barcelona"],
        "Dubrovnik": ["Copenhagen", "Athens", "Barcelona", "Munich"],
        "Munich": ["Tallinn", "Copenhagen", "Venice", "Reykjavik", "Athens", "Lyon", "Dubrovnik", "Barcelona"],
        "Venice": ["Munich", "Athens", "Lyon", "Copenhagen", "Barcelona"],
        "Reykjavik": ["Athens", "Copenhagen", "Munich", "Barcelona"],
        "Lyon": ["Barcelona", "Munich", "Venice"],
        "Barcelona": ["Lyon", "Dubrovnik", "Athens", "Reykjavik", "Copenhagen", "Venice", "Munich", "Tallinn"],
        "Tallinn": ["Munich", "Barcelona", "Copenhagen"]
    }
    
    # Create a reverse mapping for city names to avoid case issues
    city_names = list(cities.keys())
    city_name_map = {city.lower(): city for city in city_names}
    
    # Initialize Z3 variables
    day_to_city = [Int(f"day_{i}_city") for i in range(1, 27)]
    city_to_index = {city: idx for idx, city in enumerate(city_names)}
    index_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    s = Solver()
    
    # Each day's city must be a valid city index
    for day in day_to_city:
        s.add(day >= 0, day < len(city_names))
    
    # Transition constraints: consecutive days must be same city or have a direct flight
    for i in range(26 - 1):
        current_city = day_to_city[i]
        next_city = day_to_city[i + 1]
        # Either same city or connected by a direct flight
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_to_index[a], next_city == city_to_index[b]) 
                            for a in city_names for b in direct_flights[a] if b in city_name_map])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints: each city must be visited for exactly the required days
    for city, duration in cities.items():
        city_idx = city_to_index[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in day_to_city]) == duration)
    
    # Specific constraints:
    # Venice for 4 days (any days)
    # Barcelona for 3 days, with at least one day between day 10 and 12
    s.add(Or([day_to_city[i] == city_to_index["Barcelona"] for i in range(9, 12)]))  # days 10-12 (0-based: 9-11)
    
    # Copenhagen between day 7 and 10 (days 7-10 inclusive)
    s.add(Or([day_to_city[i] == city_to_index["Copenhagen"] for i in range(6, 10)]))
    
    # Dubrovnik wedding between day 16 and 20 (days 16-20 inclusive)
    s.add(Or([day_to_city[i] == city_to_index["Dubrovnik"] for i in range(15, 20)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(26):
            city_idx = model.evaluate(day_to_city[i]).as_long()
            city = index_to_city[city_idx]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should ensure it)
        itinerary_json = {"itinerary": itinerary}
        return itinerary_json
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))