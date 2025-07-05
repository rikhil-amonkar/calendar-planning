from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # Total days
    total_days = 18
    
    # Create Z3 variables: day_i represents the city on day i (1-based)
    day_vars = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day variable must be within 0..5 (representing the 6 cities)
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: total days per city must match requirements
    for city, days_needed in cities.items():
        city_id = city_ids[city]
        total = 0
        for day in day_vars:
            total += If(day == city_id, 1, 0)
        s.add(total == days_needed)
    
    # Constraint: transitions between cities must have a direct flight
    for i in range(total_days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_day == next_day)
        possible_flights = []
        for city, neighbors in direct_flights.items():
            city_id = city_ids[city]
            for neighbor in neighbors:
                neighbor_id = city_ids[neighbor]
                possible_flights.append(And(current_day == city_id, next_day == neighbor_id))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Constraint: Porto must be visited between day 16 and 18 (inclusive)
    porto_id = city_ids["Porto"]
    porto_days = []
    for i in range(16, 19):  # days 16, 17, 18 (1-based)
        day_var = day_vars[i-1]  # since day_vars is 0-based for days 1-18
        porto_days.append(day_var == porto_id)
    s.add(Or(porto_days))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Determine the sequence of cities from the model
        sequence = []
        for i in range(total_days):
            city_id = model.evaluate(day_vars[i]).as_long()
            sequence.append(id_to_city[city_id])
        
        # Generate the itinerary in the required format
        current_place = sequence[0]
        start_day = 1
        for i in range(1, total_days):
            if sequence[i] != sequence[i-1]:
                # Flight day
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {i+1}", "place": current_place})  # departure
                itinerary.append({"day_range": f"Day {i+1}", "place": sequence[i]})    # arrival
                current_place = sequence[i]
                start_day = i + 1
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))