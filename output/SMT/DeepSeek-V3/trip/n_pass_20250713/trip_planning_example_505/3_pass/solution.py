import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    
    # Direct flights as a set of tuples
    direct_flights = {('Stuttgart', 'Split'), ('Prague', 'Florence'), 
                      ('Krakow', 'Stuttgart'), ('Krakow', 'Split'), 
                      ('Split', 'Prague'), ('Krakow', 'Prague')}
    # Make sure flights are bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Days: 1 to 8
    days = list(range(1, 9))
    
    # Create Z3 variables for each day's city
    city_vars = [Int(f'day_{day}') for day in days]
    
    # Create a solver
    solver = Solver()
    
    # Each day's variable must be between 0 and 4 (representing the cities)
    for var in city_vars:
        solver.add(var >= 0, var < len(cities))
    
    # Duration constraints
    # Prague (0): 4 days
    # Stuttgart (1): 2 days
    # Split (2): 2 days
    # Krakow (3): 2 days
    # Florence (4): 2 days
    durations = {
        0: 4,  # Prague
        1: 2,  # Stuttgart
        2: 2,  # Split
        3: 2,  # Krakow
        4: 2   # Florence
    }
    
    # Count occurrences of each city in the itinerary
    for city_idx in range(len(cities)):
        solver.add(Sum([If(var == city_idx, 1, 0) for var in city_vars]) == durations[city_idx])
    
    # Flight constraints: if day i and i+1 are different, then there must be a direct flight
    for i in range(len(days) - 1):
        day1 = city_vars[i]
        day2 = city_vars[i + 1]
        # Either stay in the same city or take a direct flight
        solver.add(Or(
            day1 == day2,
            And(day1 != day2, 
                Or(*[And(day1 == a_idx, day2 == b_idx) 
                     for a_idx, a in enumerate(cities) 
                     for b_idx, b in enumerate(cities) 
                     if (a, b) in direct_flights])
        ))
    
    # Event constraints:
    # Wedding in Stuttgart between day 2 and 3: must be in Stuttgart on day 2 or 3 or both
    solver.add(Or(city_vars[1] == 1, city_vars[2] == 1))  # days are 1-based in vars (day 2 is index 1)
    
    # Meet friends in Split between day 3 and 4: must be in Split on day 3 or 4 or both
    solver.add(Or(city_vars[2] == 2, city_vars[3] == 2))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        day_assignments = []
        for day in days:
            city_idx = model.evaluate(city_vars[day - 1]).as_long()
            city = cities[city_idx]
            day_assignments.append(city)
        
        # Now, process the day assignments to create the itinerary with flight days
        current_place = day_assignments[0]
        start_day = 1
        itinerary_json = []
        
        for day in range(1, len(day_assignments) + 1):
            if day == len(day_assignments):
                # Last day
                end_day = day
                itinerary_json.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                break
            if day_assignments[day] == current_place:
                continue
            else:
                end_day = day
                itinerary_json.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                # Add the departure and arrival for the flight day
                next_place = day_assignments[day]
                itinerary_json.append({"day_range": f"Day {day}", "place": current_place})
                itinerary_json.append({"day_range": f"Day {day}", "place": next_place})
                start_day = day + 1
                current_place = next_place
        
        # Handle overlapping days for flights (if any)
        # The above loop should handle it, but let's verify
        
        # The example structure requires that flight days are separate entries for departure and arrival
        # So, the code above should handle it
        
        return {"itinerary": itinerary_json}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))