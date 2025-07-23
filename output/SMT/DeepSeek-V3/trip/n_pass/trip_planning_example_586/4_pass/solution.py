from z3 import *

def solve_itinerary():
    # Cities
    Prague, Lyon, Frankfurt, Helsinki, Naples = 0, 1, 2, 3, 4
    city_names = {
        Prague: "Prague",
        Lyon: "Lyon",
        Frankfurt: "Frankfurt",
        Helsinki: "Helsinki",
        Naples: "Naples"
    }
    
    # Direct flights: adjacency list
    direct_flights = {
        Prague: [Lyon, Frankfurt, Helsinki],
        Lyon: [Prague, Frankfurt],
        Frankfurt: [Prague, Lyon, Helsinki, Naples],
        Helsinki: [Prague, Frankfurt, Naples],
        Naples: [Helsinki, Frankfurt]
    }
    
    # Total days
    total_days = 12
    
    # Create solver
    s = Solver()
    
    # Variables: for each day, which city are we in?
    city = [Int(f'day_{i+1}_city') for i in range(total_days)]
    
    # Constraints:
    for i in range(total_days):
        s.add(city[i] >= 0, city[i] <= 4)
    
    # Flight constraints: consecutive days must be the same city or connected by direct flight
    for i in range(total_days - 1):
        s.add(Or(
            city[i] == city[i+1],
            And(city[i] != city[i+1], 
                Or([And(city[i] == a, city[i+1] == b) for a in direct_flights for b in direct_flights[a]]))
        ))
    
    # Days in each city
    def days_in_city(c):
        return Sum([If(city[i] == c, 1, 0) for i in range(total_days)])
    
    s.add(days_in_city(Frankfurt) == 3)
    s.add(days_in_city(Naples) == 4)
    s.add(days_in_city(Helsinki) == 4)
    s.add(days_in_city(Lyon) == 3)
    s.add(days_in_city(Prague) == 2)
    
    # Helsinki show from day 2 to day 5 (1-based days 2-5 are 0-based indices 1-4)
    for i in range(1, 5):
        s.add(city[i] == Helsinki)
    
    # Prague workshop between day 1 and day 2 (0-based days 0 and 1)
    s.add(Or(city[0] == Prague, city[1] == Prague))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = m.evaluate(city[0]).as_long()
        start_day = 1
        for day in range(1, total_days):
            if m.evaluate(city[day]).as_long() != current_city:
                itinerary.append({
                    'day': start_day,
                    'place': city_names[current_city]
                })
                current_city = m.evaluate(city[day]).as_long()
                start_day = day + 1
        itinerary.append({
            'day': start_day,
            'place': city_names[current_city]
        })
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

import json
result = solve_itinerary()
print(json.dumps(result, indent=2))