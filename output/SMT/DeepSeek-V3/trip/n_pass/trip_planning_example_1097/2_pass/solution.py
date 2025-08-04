from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    
    # Direct flight connections (bidirectional)
    direct_flights = {
        'Reykjavik': ['Warsaw', 'Madrid', 'Oslo', 'London'],
        'Riga': ['Warsaw', 'Oslo'],
        'Oslo': ['Madrid', 'Warsaw', 'Dubrovnik', 'Reykjavik', 'Riga', 'Lyon', 'London'],
        'Lyon': ['London', 'Oslo', 'Madrid'],
        'Dubrovnik': ['Oslo', 'Madrid'],
        'Madrid': ['Oslo', 'London', 'Lyon', 'Dubrovnik', 'Warsaw', 'Reykjavik'],
        'Warsaw': ['Reykjavik', 'Riga', 'London', 'Madrid', 'Oslo'],
        'London': ['Lyon', 'Madrid', 'Warsaw', 'Oslo', 'Reykjavik']
    }
    
    # Required days in each city
    required_days = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }
    
    # Correcting city names in required_days
    required_days['Dubrovnik'] = required_days.pop('Dubrovnik')
    required_days['Madrid'] = required_days.pop('Madrid')
    
    # Create Z3 variables for each day
    s = Solver()
    days = 18
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Each day variable must correspond to a city (0 to 7)
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: Total days per city must match required_days
    for city in cities:
        count = 0
        for day in day_vars:
            count += If(day == city_to_num[city], 1, 0)
        s.add(count == required_days[city])
    
    # Constraint: Flight connections between consecutive days
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            *[
                And(current_day == city_to_num[a], next_day == city_to_num[b])
                for a in cities
                for b in direct_flights[a]
            ]
        ))
    
    # Special constraints:
    # Riga between day 4 and 5 (i.e., day 4 or 5 is Riga)
    s.add(Or(
        day_vars[3] == city_to_num['Riga'],  # day 4 (0-based 3)
        day_vars[4] == city_to_num['Riga']   # day 5 (0-based 4)
    ))
    
    # Dubrovnik between day 7 and 8 (i.e., day 7 or 8 is Dubrovnik)
    s.add(Or(
        day_vars[6] == city_to_num['Dubrovnik'],  # day 7 (0-based 6)
        day_vars[7] == city_to_num['Dubrovnik']   # day 8 (0-based 7)
    ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, days + 1):
            day_var = day_vars[i - 1]
            city_num = m[day_var].as_long()
            city = num_to_city[city_num]
            itinerary.append({'day': i, 'place': city})
        
        # Convert to JSON
        result = {'itinerary': itinerary}
        return result
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")