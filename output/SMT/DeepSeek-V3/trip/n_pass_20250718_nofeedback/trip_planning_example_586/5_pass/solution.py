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
    
    # Variables: for each day, is there a flight? (0 = no flight, 1 = flight)
    flight = [Int(f'day_{i+1}_flight') for i in range(total_days)]
    
    # Variables: for flight days, what's the destination city?
    flight_dest = [Int(f'day_{i+1}_flight_dest') for i in range(total_days)]
    
    # Constraints:
    for i in range(total_days):
        # City must be valid
        s.add(city[i] >= 0, city[i] <= 4)
        
        # Flight can only be 0 or 1
        s.add(Or(flight[i] == 0, flight[i] == 1))
        
        # If flight, destination must be valid and connected
        s.add(Implies(flight[i] == 1, 
                     And(flight_dest[i] >= 0, flight_dest[i] <= 4,
                         flight_dest[i] != city[i],
                         Or([And(city[i] == a, flight_dest[i] == b) 
                            for a in direct_flights for b in direct_flights[a]])))
        
        # If no flight, destination is same as current city
        s.add(Implies(flight[i] == 0, flight_dest[i] == city[i]))
    
    # Flight constraints between consecutive days
    for i in range(total_days - 1):
        s.add(Or(
            # Stay in same city
            And(flight[i] == 0, city[i+1] == city[i]),
            # Take a flight
            And(flight[i] == 1, city[i+1] == flight_dest[i])
        ))
    
    # Days in each city (count both stay and flight days)
    def days_in_city(c):
        return Sum([If(Or(city[i] == c, 
                        And(flight[i] == 1, flight_dest[i] == c)), 
                   1, 0) for i in range(total_days)])
    
    s.add(days_in_city(Frankfurt) == 3)
    s.add(days_in_city(Naples) == 4)
    s.add(days_in_city(Helsinki) == 4)
    s.add(days_in_city(Lyon) == 3)
    s.add(days_in_city(Prague) == 2)
    
    # Helsinki show from day 2 to day 5 (1-based days 2-5 are 0-based indices 1-4)
    for i in range(1, 5):
        s.add(Or(city[i] == Helsinki, 
                And(flight[i] == 1, flight_dest[i] == Helsinki)))
    
    # Prague workshop between day 1 and day 2 (0-based days 0 and 1)
    s.add(Or(city[0] == Prague, 
            And(flight[0] == 1, flight_dest[0] == Prague),
            city[1] == Prague,
            And(flight[1] == 1, flight_dest[1] == Prague)))
    
    # No flights on last day
    s.add(flight[total_days-1] == 0)
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(total_days):
            current_city = m.evaluate(city[day]).as_long()
            is_flight = m.evaluate(flight[day]).as_long()
            if is_flight == 1:
                dest_city = m.evaluate(flight_dest[day]).as_long()
                itinerary.append({
                    'day': day+1,
                    'place': f"{city_names[current_city]} to {city_names[dest_city]}"
                })
            else:
                itinerary.append({
                    'day': day+1,
                    'place': city_names[current_city]
                })
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

import json
result = solve_itinerary()
print(json.dumps(result, indent=2))