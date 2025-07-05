from z3 import *
import json

def solve_trip_planning():
    # Cities to visit
    cities = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]
    
    # Required days in each city
    required_days = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Paris", "Stockholm"), ("Paris", "Seville"), ("Paris", "Zurich"), ("Paris", "Nice"),
        ("Paris", "Lyon"), ("Paris", "Riga"), ("Paris", "Naples"),
        ("Seville", "Paris"), ("Seville", "Milan"),
        ("Naples", "Zurich"), ("Naples", "Milan"), ("Naples", "Paris"), ("Naples", "Nice"), ("Naples", "Berlin"),
        ("Nice", "Riga"), ("Nice", "Paris"), ("Nice", "Zurich"), ("Nice", "Stockholm"), ("Nice", "Naples"), ("Nice", "Lyon"),
        ("Berlin", "Milan"), ("Berlin", "Stockholm"), ("Berlin", "Naples"), ("Berlin", "Zurich"), ("Berlin", "Riga"), ("Berlin", "Paris"), ("Berlin", "Nice"),
        ("Stockholm", "Paris"), ("Stockholm", "Berlin"), ("Stockholm", "Riga"), ("Stockholm", "Zurich"), ("Stockholm", "Nice"), ("Stockholm", "Milan"),
        ("Zurich", "Naples"), ("Zurich", "Paris"), ("Zurich", "Nice"), ("Zurich", "Milan"), ("Zurich", "Stockholm"), ("Zurich", "Riga"), ("Zurich", "Berlin"),
        ("Riga", "Nice"), ("Riga", "Milan"), ("Riga", "Paris"), ("Riga", "Stockholm"), ("Riga", "Zurich"), ("Riga", "Berlin"),
        ("Milan", "Berlin"), ("Milan", "Paris"), ("Milan", "Naples"), ("Milan", "Zurich"), ("Milan", "Seville"), ("Milan", "Stockholm"), ("Milan", "Riga"),
        ("Lyon", "Paris"), ("Lyon", "Nice")
    ]
    
    # Create a set of direct flight pairs for easy lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Total days
    total_days = 23
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Variables: day[i] represents the city visited on day i (1-based)
    day = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Map city names to integers for easier handling
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Each day must be assigned to a valid city
    for d in day:
        solver.add(d >= 0, d < len(cities))
    
    # Constraints for required days in each city
    for city in cities:
        count = 0
        for d in day:
            count += If(d == city_to_int[city], 1, 0)
        solver.add(count == required_days[city])
    
    # Special event constraints
    # Wedding in Berlin between day 1 and day 2 (i.e., day 1 or 2 is Berlin)
    solver.add(Or(day[0] == city_to_int["Berlin"], day[1] == city_to_int["Berlin"]))
    
    # Workshop in Nice between day 12 and 13 (i.e., day 12 or 13 is Nice)
    solver.add(Or(day[11] == city_to_int["Nice"], day[12] == city_to_int["Nice"]))
    
    # Annual show in Stockholm from day 20 to 22 (i.e., days 20, 21, 22 are Stockholm)
    solver.add(day[19] == city_to_int["Stockholm"])
    solver.add(day[20] == city_to_int["Stockholm"])
    solver.add(day[21] == city_to_int["Stockholm"])
    
    # Flight constraints: consecutive days must be either same city or have a direct flight
    for i in range(total_days - 1):
        current_city_var = day[i]
        next_city_var = day[i + 1]
        current_city = int_to_city[current_city_var]
        next_city = int_to_city[next_city_var]
        # Either stay in the same city or move to a directly connected city
        solver.add(Or(
            current_city_var == next_city_var,
            And(current_city_var != next_city_var, (current_city, next_city) in flight_pairs)
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Determine the actual days spent in each city
        day_assignments = []
        for i in range(total_days):
            city_idx = model.evaluate(day[i]).as_long()
            city = int_to_city[city_idx]
            day_assignments.append((i + 1, city))  # days are 1-based
        
        # Generate itinerary with day ranges
        current_place = day_assignments[0][1]
        start_day = 1
        for i in range(1, total_days):
            day_num, place = day_assignments[i]
            if place != current_place:
                # Add the stay up to previous day
                if start_day == day_num - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day_num - 1}", "place": current_place})
                # Add the flight day (same day for both departure and arrival)
                itinerary.append({"day_range": f"Day {day_num}", "place": current_place})
                itinerary.append({"day_range": f"Day {day_num}", "place": place})
                current_place = place
                start_day = day_num
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_trip_planning()
print(json.dumps(result, indent=2))