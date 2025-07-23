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
    
    # Variables: for each day, city1 and city2 (city2 is -1 if no flight)
    city1 = [Int(f'day_{i+1}_city1') for i in range(total_days)]
    city2 = [Int(f'day_{i+1}_city2') for i in range(total_days)]
    
    # Constraints:
    for i in range(total_days):
        s.add(city1[i] >= 0, city1[i] <= 4)
        s.add(Or(city2[i] == -1, And(city2[i] >= 0, city2[i] <= 4)))
        s.add(Or(city2[i] == -1, city2[i] != city1[i]))  # cannot fly to the same city
        # if city2[i] is not -1, then city1[i] and city2[i] must be connected by a direct flight
        s.add(Or(city2[i] == -1, 
                 Or([And(city1[i] == a, city2[i] == b) for a in direct_flights for b in direct_flights[a]])))
    
    # Days in each city
    def days_in_city(c):
        return Sum([If(Or(city1[i] == c, city2[i] == c), 1, 0) for i in range(total_days)])
    
    s.add(days_in_city(Frankfurt) == 3)
    s.add(days_in_city(Naples) == 4)
    s.add(days_in_city(Helsinki) == 4)
    s.add(days_in_city(Lyon) == 3)
    s.add(days_in_city(Prague) == 2)
    
    # Helsinki show from day 2 to day 5 (1-based days 2-5 are 0-based indices 1-4)
    for i in range(1, 5):
        s.add(Or(city1[i] == Helsinki, city2[i] == Helsinki))
    
    # Prague workshop between day 1 and day 2 (0-based days 0 and 1)
    s.add(Or(city1[0] == Prague, city2[0] == Prague, city1[1] == Prague, city2[1] == Prague))
    
    # Continuity: between day i and i+1, at least one city in day i is in day i+1
    for i in range(total_days - 1):
        s.add(Or(
            city1[i] == city1[i+1],
            city1[i] == city2[i+1],
            city2[i] == city1[i+1],
            city2[i] == city2[i+1]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, total_days + 1):
            day_index = day - 1
            c1 = m.evaluate(city1[day_index]).as_long()
            c2 = m.evaluate(city2[day_index]).as_long()
            places = [city_names[c1]]
            if c2 != -1:
                places.append(city_names[c2])
            itinerary.append({"day": day, "place": ",".join(places)})
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

import json
result = solve_itinerary()
print(json.dumps(result, indent=2))