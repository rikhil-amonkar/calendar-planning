from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    # Direct flights as adjacency list (bidirectional)
    flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Total days
    total_days = 18
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: day[i] represents the city on day i (1-based)
    day = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Assign each day variable to a city code (we'll map cities to integers)
    city_map = {city: idx for idx, city in enumerate(cities.keys())}
    city_inv_map = {idx: city for city, idx in city_map.items()}
    
    # Add constraints that each day variable is within the city codes
    for d in day:
        solver.add(d >= 0, d < len(cities))
    
    # Constraint: total days per city must match the required stay
    for city, stay in cities.items():
        city_code = city_map[city]
        solver.add(Sum([If(d == city_code, 1, 0) for d in day]) == stay)
    
    # Event constraints:
    # Bucharest days must be between day 1-4
    for i in range(total_days):
        solver.add(Implies(day[i] == city_map["Bucharest"], And(i+1 >= 1, i+1 <= 4)))
    
    # Munich wedding days must be between day 4-8
    for i in range(total_days):
        solver.add(Implies(day[i] == city_map["Munich"], And(i+1 >= 4, i+1 <= 8)))
    
    # Seville friends days must be between day 8-12
    for i in range(total_days):
        solver.add(Implies(day[i] == city_map["Seville"], And(i+1 >= 8, i+1 <= 12)))
    
    # Flight transitions: consecutive days must be connected by a direct flight or same city
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # Either stay in same city or move to connected city
        solver.add(
            Or(
                current_city == next_city,
                *[
                    And(current_city == city_map[c1], next_city == city_map[c2])
                    for c1 in flights 
                    for c2 in flights[c1]
                ]
            )
        )
    
    # Check if solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        decoded_days = [city_inv_map[model.evaluate(day[i]).as_long()] for i in range(total_days)]
        
        # Generate itinerary with proper flight day handling
        itinerary = []
        current_place = decoded_days[0]
        start_day = 1
        
        for i in range(1, total_days):
            if decoded_days[i] == decoded_days[i-1]:
                continue
            else:
                # Flight occurs between i-1 and i (0-based)
                end_day = i  # Last day in current city
                flight_day = i + 1  # 1-based day of flight
                
                # Add stay in current city
                if start_day <= end_day:
                    day_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                    itinerary.append({"day_range": day_str, "place": current_place})
                
                # Add flight day (counts for both cities)
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {flight_day}", "place": decoded_days[i]})
                
                current_place = decoded_days[i]
                start_day = flight_day + 1
        
        # Add final stay
        if start_day <= total_days:
            day_str = f"Day {start_day}-{total_days}" if start_day != total_days else f"Day {start_day}"
            itinerary.append({"day_range": day_str, "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))