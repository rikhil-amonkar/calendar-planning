from z3 import *
import json

def solve_trip_planning():
    # Cities and their required days
    cities = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos")
    ]
    
    # Total days
    total_days = 21
    
    # City names
    city_names = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    # Flight pairs (undirected)
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Z3 solver
    s = Solver()
    
    # Day variables: each day is represented by the city index
    day_city = [Int(f"day_{i}") for i in range(total_days)]
    
    # Each day's city must be a valid city index
    for day in range(total_days):
        s.add(day_city[day] >= 0)
        s.add(day_city[day] < len(city_names))
    
    # Constraints for consecutive cities: must have a flight between them
    for day in range(total_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # If different, must have a flight
        s.add(Implies(current_city != next_city,
                      Or([And(current_city == city_to_int[a], next_city == city_to_int[b])
                          for a, b in flight_pairs])))
    
    # Constraints for total days in each city
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_city[i] == city_idx, 1, 0) for i in range(total_days)]) == days)
    
    # Conference in Madrid on days 20 and 21 (0-based: 19 and 20)
    s.add(day_city[19] == city_to_int["Madrid"])
    s.add(day_city[20] == city_to_int["Madrid"])
    
    # Meeting in Stuttgart between day 1 and day 4 (0-based: 0 to 3)
    stuttgart_idx = city_to_int["Stuttgart"]
    s.add(Or([day_city[i] == stuttgart_idx for i in range(4)]))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1  # 1-based
        
        for day in range(total_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            
            if current_city is None:
                current_city = city
                start_day = day + 1
            elif city == current_city:
                continue
            else:
                if start_day == day + 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day + 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day + 1}", "place": city})
                current_city = city
                start_day = day + 1
        
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_planning()
print(json.dumps(result, indent=2))