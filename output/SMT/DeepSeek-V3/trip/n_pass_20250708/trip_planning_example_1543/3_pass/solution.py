import z3

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
    
    # Direct flights (each key has list of cities it's directly connected to)
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
    
    # Constraints for specific cities: (city, start_day, end_day)
    constraints = [
        ("Prague", 1, 3),  # must be in Prague on days 1-3 (workshop)
        ("Warsaw", 20, 23),  # must be in Warsaw between days 20-23 (friends)
        ("Porto", 16, 20),  # must be in Porto between days 16-20 (conference)
        ("London", 3, 5),   # must be in London between days 3-5 (wedding)
        ("Lisbon", 5, 9)    # must be in Lisbon between days 5-9 (relatives)
    ]
    
    total_days = 26
    days = list(range(1, total_days + 1))
    
    # Create Z3 variables: assign city to each day
    city_codes = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    code_to_city = {idx: city for city, idx in city_codes.items()}
    
    assignments = {day: z3.Int(f'day_{day}') for day in days}
    
    solver = z3.Solver()
    
    # Each day's assignment must be a valid city code
    for day in days:
        solver.add(z3.Or([assignments[day] == code for code in city_codes.values()]))
    
    # Add duration constraints: total days per city must match requirements
    for city, req_days in cities.items():
        code = city_codes[city]
        solver.add(z3.Sum([z3.If(assignments[day] == code, 1, 0) for day in days]) == req_days)
    
    # Add specific constraints for cities with fixed intervals
    for city, start, end in constraints:
        code = city_codes[city]
        # The city must be visited on all days in the interval
        for day in range(start, end + 1):
            solver.add(assignments[day] == code)
    
    # Flight constraints: consecutive days must be connected by a direct flight or same city
    for day in range(1, total_days):
        current_day_assignment = assignments[day]
        next_day_assignment = assignments[day + 1]
        solver.add(z3.Or(
            current_day_assignment == next_day_assignment,
            z3.Or([
                z3.And(current_day_assignment == city_codes[city], next_day_assignment == city_codes[adj])
                for city in direct_flights
                for adj in direct_flights[city]
            ])
        ))
    
    # Check if the solver can find a solution
    if solver.check() == z3.sat:
        model = solver.model()
        day_to_city = {}
        for day in days:
            code = model.evaluate(assignments[day]).as_long()
            city = code_to_city[code]
            day_to_city[day] = city
        
        # Generate the itinerary with proper flight days
        itinerary = []
        current_city = day_to_city[1]
        start_day = 1
        
        for day in range(2, total_days + 1):
            if day_to_city[day] != current_city:
                # Add the stay up to day-1
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                # Add the flight day (day is the transition day)
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": day_to_city[day]})
                current_city = day_to_city[day]
                start_day = day
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)