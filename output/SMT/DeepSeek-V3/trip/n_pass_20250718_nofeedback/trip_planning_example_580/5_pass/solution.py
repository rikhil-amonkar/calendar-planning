from z3 import *

def solve_itinerary():
    # Define the cities
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Paris': ['Oslo', 'Geneva', 'Porto', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Create Z3 variables for each day (1..23)
    days = 23
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day variable must be between 0 and 4 (representing the cities)
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints:
    # Days 1-7 in Geneva (indices 0..6 in 0-based days)
    for i in range(1, 8):
        s.add(day_vars[i-1] == city_to_int['Geneva'])
    
    # Days 19-23 in Oslo (indices 18..22 in 0-based)
    for i in range(19, 24):
        s.add(day_vars[i-1] == city_to_int['Oslo'])
    
    # Duration constraints:
    # Paris: 6 days
    s.add(Sum([If(day == city_to_int['Paris'], 1, 0) for day in day_vars]) == 6)
    # Oslo: 5 days (but days 19-23 are already 5 days)
    s.add(Sum([If(day == city_to_int['Oslo'], 1, 0) for day in day_vars]) == 5)
    # Porto: 7 days
    s.add(Sum([If(day == city_to_int['Porto'], 1, 0) for day in day_vars]) == 7)
    # Geneva: 7 days (days 1-7 are 7 days)
    s.add(Sum([If(day == city_to_int['Geneva'], 1, 0) for day in day_vars]) == 7)
    # Reykjavik: 2 days
    s.add(Sum([If(day == city_to_int['Reykjavik'], 1, 0) for day in day_vars]) == 2)
    
    # Flight transitions: consecutive days must be connected by direct flights or same city
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) 
              for a in direct_flights for b in direct_flights[a]]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify the durations
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Prepare the output
        output = {
            "itinerary": itinerary
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))