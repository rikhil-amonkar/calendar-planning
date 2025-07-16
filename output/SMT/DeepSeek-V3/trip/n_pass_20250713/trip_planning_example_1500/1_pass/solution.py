from z3 import *
import json

def solve_itinerary():
    cities = ["London", "Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"]
    total_days = 28
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("London", "Hamburg"), ("London", "Reykjavik"), ("Milan", "Barcelona"), 
        ("Reykjavik", "Barcelona"), ("Reykjavik", "Stuttgart"), ("Stockholm", "Reykjavik"), 
        ("London", "Stuttgart"), ("Milan", "Zurich"), ("London", "Barcelona"), 
        ("Stockholm", "Hamburg"), ("Zurich", "Barcelona"), ("Stockholm", "Stuttgart"), 
        ("Milan", "Hamburg"), ("Stockholm", "Tallinn"), ("Hamburg", "Bucharest"), 
        ("London", "Bucharest"), ("Milan", "Stockholm"), ("Stuttgart", "Hamburg"), 
        ("London", "Zurich"), ("Milan", "Reykjavik"), ("London", "Stockholm"), 
        ("Milan", "Stuttgart"), ("Stockholm", "Barcelona"), ("London", "Milan"), 
        ("Zurich", "Hamburg"), ("Bucharest", "Barcelona"), ("Zurich", "Stockholm"), 
        ("Barcelona", "Tallinn"), ("Zurich", "Tallinn"), ("Hamburg", "Barcelona"), 
        ("Stuttgart", "Barcelona"), ("Zurich", "Reykjavik"), ("Zurich", "Bucharest")
    ]
    # Make flights bidirectional and create a set of allowed transitions
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((a, b))
        allowed_transitions.add((b, a))
    for city in cities:
        allowed_transitions.add((city, city))  # staying is allowed
    
    # Required days per city
    required_days = {
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5,
        "London": 3
    }
    
    # Fixed constraints: list of (day, city)
    fixed_assignments = []
    # London days 1-3
    for day in range(1, 4):
        fixed_assignments.append((day, "London"))
    # Zurich days 7-8
    for day in range(7, 9):
        fixed_assignments.append((day, "Zurich"))
    # Reykjavik days 9-13
    for day in range(9, 14):
        fixed_assignments.append((day, "Reykjavik"))
    # Milan days 4-7 (since day 3 is London)
    for day in range(4, 8):
        fixed_assignments.append((day, "Milan"))
    
    # Create Z3 variables: day_d is the city for day d (1-based)
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}
    
    day_vars = [Int(f"day_{d}") for d in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each day variable is an index into cities
    for d in range(total_days):
        s.add(day_vars[d] >= 0, day_vars[d] < len(cities))
    
    # Apply fixed assignments
    for day, city in fixed_assignments:
        s.add(day_vars[day - 1] == city_to_int[city])
    
    # Required days per city
    for city in cities:
        count = 0
        for d in range(total_days):
            count += If(day_vars[d] == city_to_int[city], 1, 0)
        s.add(count == required_days[city])
    
    # Flight constraints: consecutive days must be same city or connected by a direct flight
    for d in range(total_days - 1):
        current_city_var = day_vars[d]
        next_city_var = day_vars[d + 1]
        # Generate allowed transitions
        constraints = []
        for a in cities:
            for b in cities:
                if (a, b) in allowed_transitions:
                    constraints.append(And(current_city_var == city_to_int[a], next_city_var == city_to_int[b]))
        s.add(Or(*constraints))
    
    if s.check() == sat:
        m = s.model()
        # Decode the day assignments
        assignments = []
        for d in range(total_days):
            city_idx = m.evaluate(day_vars[d]).as_long()
            assignments.append((d + 1, int_to_city[city_idx]))
        
        # Generate the itinerary
        itinerary = []
        i = 0
        while i < total_days:
            current_day = assignments[i][0]
            current_city = assignments[i][1]
            start_day = current_day
            # Find the range of consecutive days in the same city
            while i < total_days and assignments[i][1] == current_city:
                i += 1
            end_day = assignments[i - 1][0]
            # Add the stay entry
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
            # If not the last day and next day is a different city, add flight entries
            if i < total_days:
                next_day, next_city = assignments[i]
                # Add departure day for current city
                itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                # Add arrival day for next city
                itinerary.append({"day_range": f"Day {next_day}", "place": next_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))