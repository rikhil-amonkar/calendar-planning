from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flight connections
    connections = {
        'Krakow': ['Frankfurt', 'Oslo'],
        'Frankfurt': ['Krakow', 'Oslo', 'Dubrovnik', 'Naples'],
        'Oslo': ['Krakow', 'Frankfurt', 'Dubrovnik', 'Naples'],
        'Dubrovnik': ['Frankfurt', 'Oslo', 'Naples'],
        'Naples': ['Frankfurt', 'Oslo', 'Dubrovnik']
    }
    
    total_days = 18
    days = range(1, total_days + 1)
    
    # Create solver
    s = Solver()
    
    # Decision variables: city for each day
    day_city = [Int(f'day_{d}_city') for d in days]
    for d in days:
        s.add(day_city[d-1] >= 0, day_city[d-1] < len(cities))
    
    # Track days spent in each city (including flight days)
    city_days = [Int(f'days_in_{city}') for city in cities]
    for i, city in enumerate(cities):
        s.add(city_days[i] == Sum([If(day_city[d-1] == i, 1, 0) for d in days]))
    
    # Required days in each city
    s.add(city_days[city_idx['Krakow']] == 5)
    s.add(city_days[city_idx['Frankfurt']] == 4)
    s.add(city_days[city_idx['Oslo']] == 3)
    s.add(city_days[city_idx['Dubrovnik']] == 5)
    s.add(city_days[city_idx['Naples']] == 5)
    
    # Oslo must be days 16-18
    for d in [16, 17, 18]:
        s.add(day_city[d-1] == city_idx['Oslo'])
    
    # Dubrovnik must include at least one day between 5-9
    s.add(Or([day_city[d-1] == city_idx['Dubrovnik'] for d in range(5, 10)]))
    
    # Flight constraints
    for d in range(1, total_days):
        current = day_city[d-1]
        next_day = day_city[d]
        # If changing cities, must have direct flight
        s.add(Implies(current != next_day, 
                     Or([And(current == city_idx[c1], next_day == city_idx[c2]) 
                         for c1 in connections for c2 in connections[c1])))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current = m[day_city[0]].as_long()
        start_day = 1
        
        for d in range(1, total_days):
            next_city = m[day_city[d]].as_long()
            if next_city != current:
                itinerary.append({
                    'day_range': f'Day {start_day}-{d}',
                    'place': cities[current]
                })
                start_day = d + 1
                current = next_city
        
        itinerary.append({
            'day_range': f'Day {start_day}-{total_days}',
            'place': cities[current]
        })
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))