from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Paris': 5,
        'Warsaw': 2,
        'Krakow': 2,
        'Tallinn': 2,
        'Riga': 2,
        'Copenhagen': 5,
        'Helsinki': 5,
        'Oslo': 5,
        'Santorini': 2,
        'Lyon': 4
    }
    
    # Direct flight connections (bidirectional)
    direct_flights = {
        'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Helsinki', 'Paris', 'Krakow', 'Oslo'],
        'Riga': ['Warsaw', 'Tallinn', 'Helsinki', 'Paris', 'Oslo', 'Copenhagen', 'Krakow'],
        'Tallinn': ['Warsaw', 'Riga', 'Oslo', 'Helsinki', 'Copenhagen', 'Paris'],
        'Copenhagen': ['Helsinki', 'Warsaw', 'Lyon', 'Oslo', 'Santorini', 'Krakow', 'Riga', 'Tallinn', 'Paris'],
        'Helsinki': ['Copenhagen', 'Warsaw', 'Tallinn', 'Oslo', 'Riga', 'Krakow', 'Paris'],
        'Oslo': ['Lyon', 'Paris', 'Riga', 'Tallinn', 'Helsinki', 'Copenhagen', 'Warsaw', 'Krakow', 'Santorini'],
        'Santorini': ['Copenhagen', 'Oslo'],
        'Lyon': ['Paris', 'Oslo', 'Copenhagen'],
        'Paris': ['Lyon', 'Oslo', 'Riga', 'Tallinn', 'Warsaw', 'Copenhagen', 'Helsinki', 'Krakow'],
        'Krakow': ['Warsaw', 'Helsinki', 'Copenhagen', 'Paris', 'Oslo', 'Riga']
    }
    
    # Create solver
    s = Solver()
    
    # Day variables (1-25)
    day_vars = [Int(f'day_{day}') for day in range(1, 26)]
    
    # Each day must be assigned to a valid city
    for day in range(25):
        s.add(Or([day_vars[day] == i for i, city in enumerate(cities)]))
    
    # Flight constraints between consecutive days
    for day in range(24):
        current_city = day_vars[day]
        next_city = day_vars[day+1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == i, next_city == j)
              for i, city1 in enumerate(cities)
              for j, city2 in enumerate(cities)
              if city2 in direct_flights[city1]]
        ))
    
    # Duration constraints
    for city, days in cities.items():
        city_index = list(cities.keys()).index(city)
        s.add(Sum([If(day_vars[day] == city_index, 1, 0) for day in range(25)]) == days)
    
    # Event constraints
    paris_idx = list(cities.keys()).index('Paris')
    krakow_idx = list(cities.keys()).index('Krakow')
    riga_idx = list(cities.keys()).index('Riga')
    helsinki_idx = list(cities.keys()).index('Helsinki')
    santorini_idx = list(cities.keys()).index('Santorini')
    
    # Paris between day 4-8
    s.add(Or([day_vars[day] == paris_idx for day in range(3, 8)]))
    
    # Krakow workshop day 17-18
    s.add(Or(day_vars[16] == krakow_idx, day_vars[17] == krakow_idx))
    
    # Riga wedding day 23-24
    s.add(Or(day_vars[22] == riga_idx, day_vars[23] == riga_idx))
    
    # Helsinki friend day 18-22
    s.add(Or([day_vars[day] == helsinki_idx for day in range(17, 22)]))
    
    # Santorini relatives day 12-13
    s.add(Or(day_vars[11] == santorini_idx, day_vars[12] == santorini_idx))
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = list(cities.keys())
        for day in range(25):
            city_idx = m.evaluate(day_vars[day]).as_long()
            itinerary.append({'day': day+1, 'place': city_names[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))