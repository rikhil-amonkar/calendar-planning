import json
from z3 import *

def solve_itinerary():
    # Cities
    Prague, Stuttgart, Split, Krakow, Florence = 'Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence'
    cities = [Prague, Stuttgart, Split, Krakow, Florence]
    
    # Direct flights as adjacency list
    direct_flights = {
        Stuttgart: [Split, Krakow],
        Split: [Stuttgart, Krakow, Prague],
        Prague: [Split, Florence],
        Krakow: [Stuttgart, Split, Prague],
        Florence: [Prague]
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: for each day, which cities are visited (a list of sets)
    # Each day can have up to 2 cities (if it's a travel day)
    # We'll model this as a list of lists, where each inner list has 1 or 2 cities.
    days = 8
    itinerary = [[Int(f'day_{day}_city_{i}') for i in range(2)] for day in range(1, days + 1)]
    
    # City encodings (for the integers)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Constraints for each day: first position is always a city; second can be -1 (no city) or another city
    for day in range(days):
        day_vars = itinerary[day]
        # First city must be a valid city
        s.add(Or([day_vars[0] == city_to_int[city] for city in cities]))
        # Second city is either -1 (no travel) or a valid city different from the first
        s.add(Or(day_vars[1] == -1, 
                 And([day_vars[1] != day_vars[0],
                      Or([day_vars[1] == city_to_int[city] for city in cities])])))
    
    # Constraint: consecutive cities must have direct flights
    for day in range(days - 1):
        current_day = itinerary[day]
        next_day = itinerary[day + 1]
        
        # The last city of current day must connect to the first city of next day
        # Case 1: current day ends in one city (current_day[1] is -1)
        # Then current_day[0] must connect to next_day[0]
        case1 = And(current_day[1] == -1, 
                    Or([And(current_day[0] == city_to_int[a], next_day[0] == city_to_int[b]) 
                        for a in cities for b in direct_flights.get(a, [])]))
        # Case 2: current day is a travel day (current_day[1] is a city)
        # Then current_day[1] must connect to next_day[0]
        case2 = And(current_day[1] != -1,
                    Or([And(current_day[1] == city_to_int[a], next_day[0] == city_to_int[b])
                        for a in cities for b in direct_flights.get(a, [])]))
        s.add(Or(case1, case2))
    
    # Constraint: total days per city
    city_days = {city: 0 for city in cities}
    for city in cities:
        total = 0
        for day in range(days):
            day_vars = itinerary[day]
            # City appears in day_vars[0] or day_vars[1]
            total += If(Or(day_vars[0] == city_to_int[city], day_vars[1] == city_to_int[city]), 1, 0)
        if city == Prague:
            s.add(total == 4)
        elif city == Stuttgart:
            s.add(total == 2)
        elif city == Split:
            s.add(total == 2)
        elif city == Krakow:
            s.add(total == 2)
        elif city == Florence:
            s.add(total == 2)
    
    # Event constraints:
    # Wedding in Stuttgart between day 2 and day 3: so Stuttgart must be on day 2 or 3 (indices 1 and 2)
    stuttgart_days = []
    for day in [1, 2]:  # days are 1-based in problem, 0-based in code
        day_vars = itinerary[day]
        stuttgart_days.append(Or(day_vars[0] == city_to_int[Stuttgart], day_vars[1] == city_to_int[Stuttgart]))
    s.add(Or(stuttgart_days))
    
    # Meet friends in Split between day 3 and day 4: Split must be on day 3 or 4 (indices 2 and 3)
    split_days = []
    for day in [2, 3]:
        day_vars = itinerary[day]
        split_days.append(Or(day_vars[0] == city_to_int[Split], day_vars[1] == city_to_int[Split]))
    s.add(Or(split_days))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Decode the itinerary
        result = {'itinerary': []}
        for day in range(days):
            day_vars = itinerary[day]
            cities_day = []
            city1 = day_vars[0]
            val1 = m[city1].as_long()
            cities_day.append(int_to_city[val1])
            city2 = day_vars[1]
            val2 = m[city2].as_long() if str(city2) in [str(k) for k in m.decls()] else -1
            if val2 != -1:
                cities_day.append(int_to_city[val2])
            # For the JSON, each day is represented as the cities visited (one or two)
            day_entry = {"day": day + 1, "cities": cities_day}
            result['itinerary'].append(day_entry)
        return result
    else:
        return {"error": "No solution found"}

# Solve and print the itinerary
solution = solve_itinerary()
print(json.dumps(solution, indent=2))