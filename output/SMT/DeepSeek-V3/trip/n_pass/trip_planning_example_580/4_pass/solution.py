from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Geneva', 'Paris', 'Oslo', 'Porto', 'Reykjavik']
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    connections = [
        ('Paris', 'Oslo'),
        ('Paris', 'Geneva'),
        ('Paris', 'Porto'),
        ('Paris', 'Reykjavik'),
        ('Oslo', 'Geneva'),
        ('Oslo', 'Reykjavik'),
        ('Oslo', 'Porto'),
        ('Geneva', 'Porto')
    ]
    
    # Create adjacency list
    adjacency = {city: [] for city in cities}
    for a, b in connections:
        adjacency[a].append(b)
        adjacency[b].append(a)
    
    total_days = 23
    
    # Decision variables: city for each day
    day_city = [Int(f'day_{d}') for d in range(total_days)]
    
    s = Solver()
    
    # Each day must be assigned a valid city
    for d in range(total_days):
        s.add(day_city[d] >= 0, day_city[d] < len(cities))
    
    # Geneva must be visited on days 1-7 (0-based 0-6)
    for d in range(7):
        s.add(day_city[d] == city_idx['Geneva'])
    
    # Oslo must be visited between days 19-23 (0-based 18-22)
    for d in range(18, 23):
        s.add(day_city[d] == city_idx['Oslo'])
    
    # Count days in each city (including flight days)
    def count_days(city):
        idx = city_idx[city]
        return Sum([If(day_city[d] == idx, 1, 0) for d in range(total_days)])
    
    s.add(count_days('Paris') == 6)
    s.add(count_days('Oslo') == 5)
    s.add(count_days('Porto') == 7)
    s.add(count_days('Geneva') == 7)
    s.add(count_days('Reykjavik') == 2)
    
    # Flight transitions between consecutive days
    for d in range(total_days - 1):
        current = day_city[d]
        next_ = day_city[d + 1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_,
            *[And(current == city_idx[a], next_ == city_idx[b]) 
              for a in adjacency for b in adjacency[a]]
        ))
    
    # Initial city is Geneva
    s.add(day_city[0] == city_idx['Geneva'])
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current = cities[m.evaluate(day_city[0]).as_long()]
        start = 1
        
        for d in range(1, total_days):
            next_city = cities[m.evaluate(day_city[d]).as_long()]
            if next_city != current:
                itinerary.append({
                    'day_range': f'Day {start}-{d}',
                    'place': current
                })
                itinerary.append({
                    'day_range': f'Day {d+1}',
                    'place': f"{current}/{next_city}"
                })
                start = d + 1
                current = next_city
        
        itinerary.append({
            'day_range': f'Day {start}-{total_days}',
            'place': current
        })
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))