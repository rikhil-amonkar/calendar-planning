from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Porto', 'Amsterdam'),
        ('Amsterdam', 'Porto'),
        ('Munich', 'Amsterdam'),
        ('Amsterdam', 'Munich'),
        ('Reykjavik', 'Amsterdam'),
        ('Amsterdam', 'Reykjavik'),
        ('Munich', 'Porto'),
        ('Porto', 'Munich'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Prague'),
        ('Reykjavik', 'Munich'),
        ('Munich', 'Reykjavik'),
        ('Amsterdam', 'Santorini'),
        ('Santorini', 'Amsterdam'),
        ('Prague', 'Amsterdam'),
        ('Amsterdam', 'Prague'),
        ('Prague', 'Munich'),
        ('Munich', 'Prague')
    ]
    # Create a set of allowed city transitions
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((city_map[a], city_map[b]))
    
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
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == a, next_city == b) for (a, b) in allowed_transitions])
        ))
    
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
        current_stay_start = 1
        current_city_idx = m.evaluate(day_city[0]).as_long()
        current_city = cities[current_city_idx]
        
        for day in range(1, days + 1):
            city_idx = m.evaluate(day_city[day - 1]).as_long()
            city = cities[city_idx]
            if day == 1:
                continue
            prev_city_idx = m.evaluate(day_city[day - 2]).as_long()
            prev_city = cities[prev_city_idx]
            if city != prev_city:
                # Flight occurs between day-1 and day. So:
                # The stay in prev_city was from current_stay_start to day-1.
                itinerary.append({"day_range": f"Day {current_stay_start}-{day - 1}", "place": prev_city})
                # Flight on day: day is in both cities.
                itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_stay_start = day + 1
                current_city = city
        # Add the last stay
        if current_stay_start <= days:
            itinerary.append({"day_range": f"Day {current_stay_start}-{days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))