from z3 import *
import json

def solve_itinerary():
    # Cities with consistent naming
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Corrected direct flights adjacency list
    direct_flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Split', 'Dubrovnik'],
        'Porto': ['Munich', 'Milan'],
        'Split': ['Milan', 'Krakow', 'Munich'],
        'Milan': ['Split', 'Porto', 'Krakow', 'Munich'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    s = Solver()
    
    # Day variables (1-16)
    days = 16
    itinerary = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Each day must be one of the cities
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    # Transition constraints
    for i in range(days - 1):
        current = itinerary[i]
        next_day = itinerary[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or move via direct flight
            *[And(current == city_map[a], next_day == city_map[b])
              for a in direct_flights 
              for b in direct_flights[a]]
        ))
    
    # Total days per city
    def count_days(city):
        return Sum([If(itinerary[i] == city_map[city], 1, 0) for i in range(days)])
    
    s.add(count_days('Dubrovnik') == 4)
    s.add(count_days('Split') == 3)
    s.add(count_days('Milan') == 3)
    s.add(count_days('Porto') == 4)
    s.add(count_days('Krakow') == 2)
    s.add(count_days('Munich') == 5)
    
    # Event constraints
    # Munich show days 4-8 (indices 3-7)
    for i in range(3, 8):
        s.add(itinerary[i] == city_map['Munich'])
    
    # Milan wedding days 11-13 (indices 10-12)
    for i in range(10, 13):
        s.add(itinerary[i] == city_map['Milan'])
    
    # Krakow friends day 9 (index 8)
    s.add(itinerary[8] == city_map['Krakow'])
    
    # Find solution
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(itinerary[i]).as_long()
            city = cities[city_idx]
            result.append({"day": day_num, "place": city})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in result:
            counts[entry['place']] += 1
        
        return {"itinerary": result}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print
result = solve_itinerary()
print(json.dumps(result, indent=2))