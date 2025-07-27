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
    
    # Direct flights adjacency list (corrected for case sensitivity)
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
    
    # Create city index mapping
    city_names = sorted(cities.keys())
    city_to_index = {city: idx for idx, city in enumerate(city_names)}
    index_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    # Initialize Z3 variables
    s = Solver()
    day_to_city = [Int(f"day_{i}") for i in range(1, 27)]
    
    # Each day must be assigned to a valid city
    for day in day_to_city:
        s.add(day >= 0, day < len(city_names))
    
    # Transition constraints with flight day counting
    for i in range(25):
        current = day_to_city[i]
        next_day = day_to_city[i+1]
        
        # Either stay in same city or fly to connected city
        same_city = current == next_day
        possible_flights = []
        for city in city_names:
            if city in direct_flights:
                for dest in direct_flights[city]:
                    if dest in city_to_index:
                        possible_flights.append(And(
                            current == city_to_index[city],
                            next_day == city_to_index[dest]
                        ))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Duration constraints
    for city, duration in cities.items():
        city_idx = city_to_index[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in day_to_city]) == duration)
    
    # Specific date range constraints
    # Barcelona between days 10-12 (inclusive)
    s.add(Or([day_to_city[i] == city_to_index["Barcelona"] for i in range(9, 12)]))
    
    # Copenhagen between days 7-10 (inclusive)
    s.add(Or([day_to_city[i] == city_to_index["Copenhagen"] for i in range(6, 10)]))
    
    # Dubrovnik between days 16-20 (inclusive)
    s.add(Or([day_to_city[i] == city_to_index["Dubrovnik"] for i in range(15, 20)]))
    
    # Additional constraints to help the solver
    # Ensure first day starts in a city with many connections
    s.add(Or(
        day_to_city[0] == city_to_index["Copenhagen"],
        day_to_city[0] == city_to_index["Barcelona"],
        day_to_city[0] == city_to_index["Munich"]
    ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(26):
            city_idx = model.evaluate(day_to_city[i]).as_long()
            city = index_to_city[city_idx]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify all constraints are met
        city_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            city_counts[entry["place"]] += 1
        
        for city, count in city_counts.items():
            assert count == cities[city], f"Duration mismatch for {city}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))