from z3 import *

def solve_itinerary():
    # Cities to visit with their required days
    cities = {
        "Mykonos": 4,
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Dubrovnik": 3,
        "Oslo": 2,
        "Madrid": 5,
        "Paris": 2
    }
    
    # Direct flights: adjacency list (bidirectional)
    direct_flights = {
        "Oslo": ["Krakow", "Paris", "Madrid", "Helsinki", "Dubrovnik", "Vilnius"],
        "Krakow": ["Oslo", "Paris", "Vilnius", "Helsinki"],
        "Paris": ["Oslo", "Madrid", "Krakow", "Helsinki", "Vilnius"],
        "Helsinki": ["Vilnius", "Oslo", "Krakow", "Dubrovnik", "Paris", "Madrid"],
        "Vilnius": ["Helsinki", "Oslo", "Paris", "Krakow"],
        "Dubrovnik": ["Helsinki", "Madrid", "Oslo"],
        "Madrid": ["Paris", "Oslo", "Helsinki", "Dubrovnik", "Mykonos"],
        "Mykonos": ["Madrid"]
    }
    
    # Total days
    total_days = 18
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Variables: for each day, which city are we in?
    day_place = [Int(f"day_{d+1}") for d in range(total_days)]
    
    # City encodings
    city_names = sorted(cities.keys())
    city_ids = {city: idx for idx, city in enumerate(city_names)}
    id_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    # Add constraints: each day_place must be a valid city ID
    for d in range(total_days):
        solver.add(day_place[d] >= 0, day_place[d] < len(city_names))
    
    # Constraints for consecutive days: transitions must be via direct flights
    for d in range(total_days - 1):
        current_city = day_place[d]
        next_city = day_place[d+1]
        # Either stay in same city or move to connected city
        solver.add(Or(
            current_city == next_city,
            Or([And(current_city == city_ids[src], next_city == city_ids[dest])
               for src in direct_flights for dest in direct_flights[src]])
        ))
    
    # Fixed day constraints
    # Oslo on day 1
    solver.add(day_place[0] == city_ids["Oslo"])
    # Dubrovnik from day 2-4 (days 2,3,4)
    solver.add(day_place[1] == city_ids["Dubrovnik"])
    solver.add(day_place[2] == city_ids["Dubrovnik"])
    solver.add(day_place[3] == city_ids["Dubrovnik"])
    # Mykonos from day 15-18 (days 15,16,17,18)
    solver.add(day_place[14] == city_ids["Mykonos"])
    solver.add(day_place[15] == city_ids["Mykonos"])
    solver.add(day_place[16] == city_ids["Mykonos"])
    solver.add(day_place[17] == city_ids["Mykonos"])
    
    # Total days per city
    for city, days in cities.items():
        solver.add(Sum([If(day_place[d] == city_ids[city], 1, 0) 
                      for d in range(total_days)]) == days)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Extract the itinerary
        itinerary = []
        
        # Track current city and start day
        current_city = None
        start_day = 1
        
        for d in range(total_days):
            city_id = model.evaluate(day_place[d]).as_long()
            city = id_to_city[city_id]
            
            if d == 0:
                current_city = city
                start_day = 1
            else:
                prev_city_id = model.evaluate(day_place[d-1]).as_long()
                prev_city = id_to_city[prev_city_id]
                
                if city != prev_city:
                    # Add previous city's stay
                    if start_day <= d:
                        itinerary.append({"day_range": f"Day {start_day}-{d}", "place": prev_city})
                    # Add flight day entries
                    itinerary.append({"day_range": f"Day {d+1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {d+1}", "place": city})
                    start_day = d + 2
                    current_city = city
        
        # Add last stay
        if start_day <= total_days:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))