import z3
from collections import defaultdict

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
    direct_flights = {
        "Warsaw": ["Vilnius", "London", "Athens", "Lisbon", "Porto", "Prague", "Dublin"],
        "Vilnius": ["Warsaw", "Athens"],
        "Prague": ["Athens", "Lisbon", "London", "Warsaw", "Dublin"],
        "Athens": ["Prague", "Vilnius", "Dublin", "Warsaw", "Dubrovnik", "Lisbon", "London"],
        "London": ["Lisbon", "Dublin", "Prague", "Warsaw", "Athens"],
        "Lisbon": ["London", "Porto", "Prague", "Athens", "Warsaw", "Dublin", "Seville"],
        "Porto": ["Lisbon", "Seville", "Warsaw", "Dublin"],
        "Dublin": ["London", "Seville", "Athens", "Prague", "Dubrovnik", "Lisbon", "Porto"],
        "Seville": ["Dublin", "Porto", "Lisbon"],
        "Dubrovnik": ["Athens", "Dublin"]
    }
    
    # Fixed constraints
    fixed_periods = [
        ("Prague", 1, 3),   # Days 1-3 in Prague
        ("London", 3, 5),   # Days 3-5 in London
        ("Lisbon", 5, 9),   # Days 5-9 in Lisbon
        ("Porto", 16, 20),  # Days 16-20 in Porto
        ("Warsaw", 20, 23)  # Days 20-23 in Warsaw
    ]
    
    total_days = 26
    days = list(range(1, total_days + 1))
    
    # Create Z3 variables
    city_codes = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    code_to_city = {idx: city for city, idx in city_codes.items()}
    
    assignments = {day: z3.Int(f'day_{day}') for day in days}
    
    solver = z3.Solver()
    
    # Assign fixed periods first
    for city, start, end in fixed_periods:
        code = city_codes[city]
        for day in range(start, end + 1):
            solver.add(assignments[day] == code)
    
    # Each day must be assigned to a valid city
    for day in days:
        solver.add(z3.Or([assignments[day] == code for code in city_codes.values()]))
    
    # Duration constraints for all cities
    for city, req_days in cities.items():
        code = city_codes[city]
        solver.add(z3.Sum([z3.If(assignments[day] == code, 1, 0) for day in days]) == req_days)
    
    # Flight constraints between consecutive days
    for day in range(1, total_days):
        current = assignments[day]
        next_day = assignments[day + 1]
        solver.add(z3.Or(
            current == next_day,  # Stay in same city
            z3.Or([  # Or take a direct flight
                z3.And(current == city_codes[city], next_day == city_codes[adj])
                for city in direct_flights
                for adj in direct_flights[city]
            ])
        ))
    
    # Additional constraints to ensure all cities are visited
    for city in cities:
        code = city_codes[city]
        solver.add(z3.Or([assignments[day] == code for day in days]))
    
    # Check solution
    if solver.check() == z3.sat:
        model = solver.model()
        schedule = [code_to_city[model.evaluate(assignments[day]).as_long()] for day in days]
        
        # Generate itinerary
        itinerary = []
        current_city = schedule[0]
        start_day = 1
        
        for day in range(1, total_days):
            if schedule[day] != current_city:
                # Add stay period
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                # Add flight day
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": schedule[day]})
                current_city = schedule[day]
                start_day = day + 1
        
        # Add last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {total_days}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Verify total days
        total_itinerary_days = 0
        for entry in itinerary:
            if '-' in entry['day_range']:
                start, end = map(int, entry['day_range'].replace('Day ', '').split('-'))
                total_itinerary_days += (end - start + 1)
            else:
                total_itinerary_days += 1
        
        if total_itinerary_days != total_days:
            return {"error": f"Total days mismatch: expected {total_days}, got {total_itinerary_days}"}
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)