from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Total days
    total_days = 20
    
    # Create Z3 variables: assign each day to a city or a transition
    # day_assignments[d][0] = departure city (if flying), day_assignments[d][1] = arrival city (if flying)
    # Otherwise, same city for both.
    s = Solver()
    
    # For each day, we have a current city and possibly a next city if flying.
    # day_city[d] represents the city on day d (1-based)
    day_city = [Int(f'day_{d}_city') for d in range(1, total_days + 1)]
    
    # Each day_city must be 0-3 (Valencia, Athens, Naples, Zurich)
    for d in range(total_days):
        s.add(day_city[d] >= 0, day_city[d] <= 3)
    
    # Flight transitions: if day d and d+1 are different, then there's a flight between them.
    # Also, flights must be direct.
    direct_flights = [
        (0, 1), (1, 0),  # Valencia <-> Athens
        (0, 2), (2, 0),  # Valencia <-> Naples
        (1, 2), (2, 1),  # Athens <-> Naples
        (1, 3), (3, 1),  # Athens <-> Zurich
        (2, 3), (3, 2),  # Naples <-> Zurich
        (0, 3), (3, 0)   # Valencia <-> Zurich
    ]
    
    for d in range(total_days - 1):
        current = day_city[d]
        next_ = day_city[d + 1]
        # Either stay in the same city or take a direct flight
        s.add(Or(current == next_, *[And(current == a, next_ == b) for (a, b) in direct_flights]))
    
    # Constraints on total days per city
    valencia_days = sum([If(day_city[d] == 0, 1, 0) for d in range(total_days)])
    athens_days = sum([If(day_city[d] == 1, 1, 0) for d in range(total_days)])
    naples_days = sum([If(day_city[d] == 2, 1, 0) for d in range(total_days)])
    zurich_days = sum([If(day_city[d] == 3, 1, 0) for d in range(total_days)])
    
    s.add(valencia_days == 6)
    s.add(athens_days == 6)
    s.add(naples_days == 5)
    s.add(zurich_days == 6)
    
    # Athens between day 1 and day 6 (1-based days 0-5 in zero-based)
    # At least one day in Athens in days 0-5 (1-6 in 1-based)
    s.add(Or(*[day_city[d] == 1 for d in range(6)]))
    
    # Naples wedding between day 16 and 20 (1-based days 15-19 in zero-based)
    s.add(Or(*[day_city[d] == 2 for d in range(15, 20)]))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the day assignments
        schedule = []
        for d in range(total_days):
            city_idx = m.evaluate(day_city[d]).as_long()
            schedule.append(cities[city_idx])
        
        # Now, build the itinerary with day ranges and flight days
        itinerary = []
        current_city = schedule[0]
        start_day = 1  # 1-based
        
        for d in range(1, total_days):
            if schedule[d] != schedule[d-1]:
                # Flight occurs between d-1 and d (1-based days d and d+1)
                # Add the departure city's stay up to d (1-based day d)
                end_day = d  # 1-based
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                # Add the flight day entries for both cities
                itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                itinerary.append({"day_range": f"Day {end_day}", "place": schedule[d]})
                # Update current city and start day
                current_city = schedule[d]
                start_day = end_day + 1  # since end_day is the day of flight
            # else continue the current city
        # Add the last segment
        end_day = total_days
        if start_day == end_day:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))