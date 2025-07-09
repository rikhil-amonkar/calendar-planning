from z3 import *

def solve_itinerary():
    s = Solver()

    # Define cities and their required days
    cities = ['Dublin', 'Riga', 'Vilnius']
    required_days = {'Dublin': 2, 'Riga': 5, 'Vilnius': 7}
    
    # Flight connections (bidirectional)
    flights = {
        'Dublin': ['Riga'],
        'Riga': ['Dublin', 'Vilnius'],
        'Vilnius': ['Riga']
    }

    # Create day variables (1-12)
    day_assignments = [Int(f'day_{i}') for i in range(1, 13)]
    city_to_int = {city: i for i, city in enumerate(cities)}
    
    # Each day must be assigned to a valid city
    for day in day_assignments:
        s.add(Or([day == city_to_int[city] for city in cities]))

    # Count days in each city (must match requirements)
    for city in cities:
        count = Sum([If(day == city_to_int[city], 1, 0) for day in day_assignments])
        s.add(count == required_days.get(city, 0))

    # Flight constraints between consecutive days
    for i in range(11):
        current = day_assignments[i]
        next_day = day_assignments[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or take a valid flight
            Or([And(current == city_to_int[depart], 
                next_day == city_to_int[arrive])
                for depart in flights 
                for arrive in flights[depart]])
        ))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1

        for day in range(1, 13):
            city_idx = model.evaluate(day_assignments[day-1]).as_long()
            city = cities[city_idx]
            
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add stay period for previous city
                if start_day == day-1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                
                # Add flight day (both departure and arrival)
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                
                current_city = city
                start_day = day

        # Add final stay period
        if start_day == 12:
            itinerary.append({"day_range": f"Day 12", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-12", "place": current_city})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the solution
itinerary = solve_itinerary()
print(itinerary)