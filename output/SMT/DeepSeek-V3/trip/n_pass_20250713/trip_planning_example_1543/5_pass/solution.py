from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3
    }
    
    # Direct flights (bidirectional)
    flight_connections = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens")
    ]
    
    # Fixed events (city, start_day, end_day)
    fixed_events = [
        ("Prague", 1, 3),
        ("London", 3, 5),
        ("Lisbon", 5, 9),
        ("Porto", 16, 20),
        ("Warsaw", 20, 23)
    ]
    
    total_days = 26
    num_days = total_days
    
    # Create Z3 variables for each day's city
    day_city = [Int(f"day_{i}") for i in range(1, num_days + 1)]
    
    # City ID mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for dc in day_city:
        s.add(And(dc >= 0, dc < len(cities)))
    
    # Add fixed event constraints
    for city, start, end in fixed_events:
        city_id = city_ids[city]
        for day in range(start, end + 1):
            s.add(day_city[day - 1] == city_id)
    
    # Ensure required days per city
    for city, req_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_city[i] == city_id, 1, 0) for i in range(num_days)]) == req_days)
    
    # Flight constraints between consecutive days
    for i in range(num_days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        
        # Either stay in same city or take direct flight
        same_city = current == next_day
        flight_options = []
        
        # Check all possible flight connections
        for city1, city2 in flight_connections:
            c1 = city_ids[city1]
            c2 = city_ids[city2]
            flight_options.append(And(current == c1, next_day == c2))
            flight_options.append(And(current == c2, next_day == c1))
        
        s.add(Or(same_city, Or(flight_options)))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, num_days + 1):
            city_id = m.evaluate(day_city[day - 1]).as_long()
            city = id_to_city[city_id]
            
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add previous stay
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                
                # Add flight day (both cities)
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                
                current_city = city
                start_day = day
            
            # Last day
            if day == num_days:
                if start_day == day:
                    itinerary.append({"day_range": f"Day {day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
        
        # Verify day counts
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                days = end - start + 1
            else:
                days = 1
            city_days[place] += days
        
        for city in cities:
            assert city_days[city] == cities[city], f"Day count mismatch for {city}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))