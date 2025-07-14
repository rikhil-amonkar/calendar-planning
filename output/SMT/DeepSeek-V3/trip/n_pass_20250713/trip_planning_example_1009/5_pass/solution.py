from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Bucharest", "Vienna"),
        ("Reykjavik", "Vienna"),
        ("Manchester", "Vienna"),
        ("Manchester", "Riga"),
        ("Riga", "Vienna"),
        ("Istanbul", "Vienna"),
        ("Vienna", "Florence"),
        ("Stuttgart", "Vienna"),
        ("Riga", "Bucharest"),
        ("Istanbul", "Riga"),
        ("Stuttgart", "Istanbul"),
        ("Reykjavik", "Stuttgart"),
        ("Istanbul", "Bucharest"),
        ("Manchester", "Istanbul"),
        ("Manchester", "Bucharest"),
        ("Stuttgart", "Manchester")
    ]
    
    # Create a set of all possible direct flight connections (bidirectional)
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))
    
    # Total days
    total_days = 23
    
    # Workshop and show constraints
    workshop_bucharest_days = [16, 17, 18, 19]  # must be in Bucharest on at least one of these days
    show_istanbul_days = [12, 13]  # must be in Istanbul on these days
    
    # Create Z3 variables
    day_to_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day's city must be one of the 8 cities
    for day_var in day_to_city:
        s.add(Or([day_var == city_ids[city] for city in cities]))
    
    # Constraints for total days per city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_var == city_id, 1, 0) for day_var in day_to_city]) == required_days)
    
    # Workshop in Bucharest between day 16 and 19 (inclusive)
    # Must be in Bucharest for at least one day in this range
    s.add(Or([day_to_city[d-1] == city_ids["Bucharest"] for d in workshop_bucharest_days]))
    
    # Show in Istanbul on days 12 and 13
    s.add(day_to_city[11] == city_ids["Istanbul"])  # day 12
    s.add(day_to_city[12] == city_ids["Istanbul"])  # day 13
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(total_days - 1):
        current_city_var = day_to_city[i]
        next_city_var = day_to_city[i+1]
        s.add(Or(
            current_city_var == next_city_var,
            And(current_city_var != next_city_var, 
                Or([And(current_city_var == city_ids[a], next_city_var == city_ids[b]) 
                    for a, b in flight_connections if a in cities and b in cities]))
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        # Generate the itinerary day by day
        for day in range(1, total_days + 1):
            city_id = model.evaluate(day_to_city[day-1]).as_long()
            city = id_to_city[city_id]
            
            if day == 1:
                current_city = city
                start_day = 1
            else:
                prev_city_id = model.evaluate(day_to_city[day-2]).as_long()
                prev_city = id_to_city[prev_city_id]
                if city != prev_city:
                    # Add the previous city's stay up to day-1
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": prev_city})
                    # Add the flight day entries for day (day is both prev_city and city)
                    itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                    start_day = day
                    current_city = city
        
        # Add the last city's stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Verify total days
        total_days_check = 0
        for entry in itinerary:
            if '-' in entry['day_range']:
                start, end = map(int, entry['day_range'].split('-'))
                total_days_check += end - start + 1
            else:
                total_days_check += 1
        
        if total_days_check != total_days:
            return {"error": f"Total days constraint not met (got {total_days_check}, expected {total_days})"}
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))