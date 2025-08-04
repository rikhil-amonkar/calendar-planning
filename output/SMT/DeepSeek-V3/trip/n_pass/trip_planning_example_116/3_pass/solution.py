from z3 import *

def solve_itinerary():
    # Cities
    Split, Santorini, London = Ints('Split Santorini London')
    cities = {'Split': Split, 'Santorini': Santorini, 'London': London}
    
    # Days are 1..18
    days = 18
    # For each day, which city are we in?
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Assign each city a unique integer
    city_ids = { 'Split': 0, 'Santorini': 1, 'London': 2 }
    id_to_city = { 0: 'Split', 1: 'Santorini', 2: 'London' }
    
    # Each day's city must be one of the three cities
    for day in day_city:
        s.add(Or(day == city_ids['Split'], day == city_ids['Santorini'], day == city_ids['London']))
    
    # Flight constraints: transitions only between connected cities
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        # Possible transitions:
        # Split <-> London, London <-> Santorini
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == city_ids['Split'], next_day == city_ids['London']),
            And(current == city_ids['London'], next_day == city_ids['Split']),
            And(current == city_ids['London'], next_day == city_ids['Santorini']),
            And(current == city_ids['Santorini'], next_day == city_ids['London'])
        ))
    
    # Total days per city
    split_days = Sum([If(day == city_ids['Split'], 1, 0) for day in day_city])
    santorini_days = Sum([If(day == city_ids['Santorini'], 1, 0) for day in day_city])
    london_days = Sum([If(day == city_ids['London'], 1, 0) for day in day_city])
    
    s.add(split_days == 6)
    s.add(santorini_days == 7)
    s.add(london_days == 7)
    
    # Santorini must be visited on day 12 and day 18 (1-based)
    s.add(day_city[11] == city_ids['Santorini'])  # day 12 is index 11
    s.add(day_city[17] == city_ids['Santorini'])  # day 18 is index 17
    
    # Ensure that the first day is in one of the cities
    s.add(Or(day_city[0] == city_ids['Split'], day_city[0] == city_ids['London'], day_city[0] == city_ids['Santorini']))
    
    # Ensure that the last day is in Santorini (as per day 18 constraint)
    s.add(day_city[17] == city_ids['Santorini'])
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_id = m.evaluate(day_city[i]).as_long()
            city_name = id_to_city[city_id]
            itinerary.append({'day': i + 1, 'place': city_name})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))