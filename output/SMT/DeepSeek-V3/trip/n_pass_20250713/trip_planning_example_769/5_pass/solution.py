from z3 import *

def solve_itinerary():
    # Cities with correct spelling
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Porto', 'Amsterdam'),
        ('Munich', 'Amsterdam'),
        ('Reykjavik', 'Amsterdam'),
        ('Munich', 'Porto'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Amsterdam', 'Santorini'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Munich')
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day 1 to 16, each day is a city
    days = 16
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    # Each day's city must be 0-5 (mapped to cities)
    for dc in day_city:
        s.add(dc >= 0)
        s.add(dc <= 5)
    
    # Flight transitions: consecutive days must be either same city or connected by direct flight
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either same city or flight exists
        transition_constraints = []
        for a, b in direct_flights:
            transition_constraints.append(And(current_city == city_map[a], next_city == city_map[b]))
            transition_constraints.append(And(current_city == city_map[b], next_city == city_map[a]))
        s.add(Or(current_city == next_city, Or(transition_constraints)))
    
    # Total days per city constraints
    total_days = [Int(f'total_{city}') for city in cities]
    for city_idx, city in enumerate(cities):
        s.add(total_days[city_idx] == Sum([If(day_city[i] == city_idx, 1, 0) for i in range(days)]))
    
    s.add(total_days[city_map['Porto']] == 5)
    s.add(total_days[city_map['Prague']] == 4)
    s.add(total_days[city_map['Reykjavik']] == 4)
    s.add(total_days[city_map['Santorini']] == 2)
    s.add(total_days[city_map['Amsterdam']] == 2)
    s.add(total_days[city_map['Munich']] == 4)
    
    # Event constraints
    # Wedding in Reykjavik between day 4 and 7 (1-based days 4-7: indices 3-6)
    s.add(Or([day_city[i] == city_map['Reykjavik'] for i in [3, 4, 5, 6]]))
    
    # Conference in Amsterdam on day 14 and 15 (1-based: days 14-15 are indices 13-14)
    s.add(day_city[13] == city_map['Amsterdam'])
    s.add(day_city[14] == city_map['Amsterdam'])
    
    # Friend in Munich between day 7 and 10 (1-based days 7-10: indices 6-9)
    s.add(Or([day_city[i] == city_map['Munich'] for i in [6, 7, 8, 9]]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Generate the itinerary
        itinerary = []
        current_stay = []
        
        for day in range(1, days + 1):
            city_idx = m.evaluate(day_city[day - 1]).as_long()
            city = cities[city_idx]
            current_stay.append((day, city))
        
        # Process stays and flights
        i = 0
        while i < len(current_stay):
            start_day, city = current_stay[i]
            j = i + 1
            while j < len(current_stay) and current_stay[j][1] == city:
                j += 1
            end_day = current_stay[j - 1][0]
            
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            
            # Add flight day if there's a transition
            if j < len(current_stay):
                next_city = current_stay[j][1]
                itinerary.append({"day_range": f"Day {end_day}", "place": city})
                itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
            
            i = j
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))