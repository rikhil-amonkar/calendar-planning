from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Dublin", "London", "Hamburg", "Helsinki", "Reykjavik", "Mykonos"]
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Corrected direct flights (fixed typo in "Helsinki")
    direct_flights = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London")
    ]
    
    # Create flight connections
    flight_connections = {}
    for city in cities:
        flight_connections[city] = []
    for a, b in direct_flights:
        flight_connections[a].append(b)
        flight_connections[b].append(a)
    
    # Days: 1 to 16
    days = 16
    day_range = range(1, days + 1)
    
    # Z3 variables
    city_vars = [Int(f"day_{day}") for day in day_range]
    flight_vars = [Bool(f"flight_{day}") for day in day_range[:-1]]  # Flight between day and day+1
    
    s = Solver()
    
    # Each day must be a valid city
    for var in city_vars:
        s.add(var >= 0, var < len(cities))
    
    # Fixed constraints
    # Days 1-2: Hamburg
    s.add(city_vars[0] == city_map["Hamburg"])
    s.add(city_vars[1] == city_map["Hamburg"])
    
    # Days 3-6: Dublin (annual show)
    for day in [2,3,4,5]:  # Days 3-6 (0-based index 2-5)
        s.add(city_vars[day] == city_map["Dublin"])
    
    # Days 9-10: Reykjavik (wedding)
    s.add(city_vars[8] == city_map["Reykjavik"])  # Day 9
    s.add(city_vars[9] == city_map["Reykjavik"])  # Day 10
    
    # Flight constraints
    for day in range(days - 1):
        current_city = city_vars[day]
        next_city = city_vars[day + 1]
        
        # If cities are different, must be connected by flight
        s.add(Implies(
            current_city != next_city,
            Or([And(current_city == city_map[a], next_city == city_map[b]) 
                for a in cities for b in flight_connections[a]])
        ))
        
        # Flight variable is true when cities change
        s.add(flight_vars[day] == (current_city != next_city))
    
    # Duration constraints
    # Dublin: 5 days total (already have 4 from days 3-6)
    dublin_days = Sum([If(city_vars[i] == city_map["Dublin"], 1, 0) for i in range(days)])
    s.add(dublin_days == 5)
    
    # London: 5 days
    london_days = Sum([If(city_vars[i] == city_map["London"], 1, 0) for i in range(days)])
    s.add(london_days == 5)
    
    # Helsinki: 4 days
    helsinki_days = Sum([If(city_vars[i] == city_map["Helsinki"], 1, 0) for i in range(days)])
    s.add(helsinki_days == 4)
    
    # Reykjavik: 2 days (already have 2 from days 9-10)
    reykjavik_days = Sum([If(city_vars[i] == city_map["Reykjavik"], 1, 0) for i in range(days)])
    s.add(reykjavik_days == 2)
    
    # Mykonos: 3 days
    mykonos_days = Sum([If(city_vars[i] == city_map["Mykonos"], 1, 0) for i in range(days)])
    s.add(mykonos_days == 3)
    
    # Hamburg: 2 days (already have 2 from days 1-2)
    hamburg_days = Sum([If(city_vars[i] == city_map["Hamburg"], 1, 0) for i in range(days)])
    s.add(hamburg_days == 2)
    
    # Solve and create itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, days + 1):
            city_idx = m[city_vars[day - 1]].as_long()
            city = cities[city_idx]
            
            if city != current_city:
                if current_city is not None:
                    # Add previous stay
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                    # Add flight day
                    itinerary.append({"day_range": f"Day {day}", "place": current_city})
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                start_day = day
                current_city = city
        
        # Add final stay
        if start_day == days:
            itinerary.append({"day_range": f"Day {days}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print
print(solve_itinerary())