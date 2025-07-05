from z3 import *
import json

def solve_scheduling():
    cities = ["Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik", "Stuttgart", 
              "Stockholm", "Tallinn", "Milan", "London"]
    
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
    
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    
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
    
    fixed_constraints = [
        ("London", 1, 3),
        ("Milan", 3, 7),
        ("Zurich", 7, 8),
        ("Reykjavik", 9, 13)
    ]
    
    day_vars = [Int(f"day_{i}") for i in range(1, 29)]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    s = Solver()
    
    for day_var in day_vars:
        s.add(day_var >= 0, day_var < len(cities))
    
    for (city, start, end) in fixed_constraints:
        city_idx = city_indices[city]
        for day in range(start, end + 1):
            s.add(day_vars[day - 1] == city_idx)
    
    for city in cities:
        city_idx = city_indices[city]
        total_days = Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(28)])
        s.add(total_days == required_days[city])
    
    for i in range(27):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        same_city = current_day == next_day
        flight_exists = Or([And(current_day == city_indices[a], next_day == city_indices[b]) 
                           for (a, b) in bidirectional_flights])
        s.add(Or(same_city, flight_exists))
    
    if s.check() == sat:
        m = s.model()
        day_assignments = []
        for i in range(28):
            day = i + 1
            city_idx = m.evaluate(day_vars[i]).as_long()
            city = cities[city_idx]
            day_assignments.append(city)
        
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        
        for day in range(1, 28):
            if day_assignments[day] != current_city:
                # Add the stay up to day
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                # Add the flight day (day is the transition day)
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": day_assignments[day]})
                current_city = day_assignments[day]
                start_day = day + 1
        
        # Add the last stay
        if start_day <= 28:
            if start_day == 28:
                itinerary.append({"day_range": f"Day {28}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{28}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))