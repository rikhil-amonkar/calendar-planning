from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities and their codes
    cities = ['Dubrovnik', 'Frankfurt', 'Krakow']
    city_map = {c: i for i, c in enumerate(cities)}
    
    # Day assignments (1-10)
    day_city = [Int(f'day_{i}') for i in range(1, 11)]
    
    # Each day must be assigned to a valid city
    for day in day_city:
        s.add(Or([day == city_map[c] for c in cities]))
    
    # Flight constraints - only direct connections allowed
    for i in range(9):  # Check transitions between days
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(  # Dubrovnik <-> Frankfurt
                Or(current == city_map['Dubrovnik'], current == city_map['Frankfurt']),
                Or(next_day == city_map['Dubrovnik'], next_day == city_map['Frankfurt'])
            ),
            And(  # Frankfurt <-> Krakow
                Or(current == city_map['Frankfurt'], current == city_map['Krakow']),
                Or(next_day == city_map['Frankfurt'], next_day == city_map['Krakow'])
            )
        ))
    
    # Count days in each city
    dubrovnik_days = sum([If(day == city_map['Dubrovnik'], 1, 0) for day in day_city])
    frankfurt_days = sum([If(day == city_map['Frankfurt'], 1, 0) for day in day_city])
    krakow_days = sum([If(day == city_map['Krakow'], 1, 0) for day in day_city])
    
    # Add day count constraints
    s.add(dubrovnik_days == 7)
    s.add(frankfurt_days == 3)
    s.add(krakow_days == 2)
    
    # Wedding must be on day 9 or 10 in Krakow
    s.add(Or(day_city[8] == city_map['Krakow'], day_city[9] == city_map['Krakow']))
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(10):
            city_code = m.evaluate(day_city[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_code]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))