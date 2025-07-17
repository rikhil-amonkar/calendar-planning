from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (undirected)
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
    
    # Create adjacency list
    adjacency = [[] for _ in cities]
    for a, b in direct_flights:
        adjacency[city_idx[a]].append(city_idx[b])
        adjacency[city_idx[b]].append(city_idx[a])
    
    # Z3 variables: day[i] is city index for day i+1 (1-based)
    days = [Int(f'day_{i}') for i in range(16)]
    
    s = Solver()
    
    # Each day must be a valid city
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Transition constraints
    for i in range(15):
        current = days[i]
        next_day = days[i+1]
        # Either stay or move to connected city
        s.add(Or(
            current == next_day,
            Or([next_day == adj for adj in adjacency[current.as_long()] if current.is_int() else True)
        ))
    
    # Duration constraints
    for city in cities:
        count = Sum([If(days[i] == city_idx[city], 1, 0) for i in range(16)])
        if city == 'Porto':
            s.add(count == 5)
        elif city == 'Prague':
            s.add(count == 4)
        elif city == 'Reykjavik':
            s.add(count == 4)
        elif city == 'Santorini':
            s.add(count == 2)
        elif city == 'Amsterdam':
            s.add(count == 2)
        elif city == 'Munich':
            s.add(count == 4)
    
    # Fixed events
    # Wedding in Reykjavik between day 4-7
    s.add(Or([days[i] == city_idx['Reykjavik'] for i in range(3, 7)]))
    
    # Conference in Amsterdam on day 14-15
    s.add(days[13] == city_idx['Amsterdam'])
    s.add(days[14] == city_idx['Amsterdam'])
    
    # Meet friend in Munich between day 7-10
    s.add(Or([days[i] == city_idx['Munich'] for i in range(6, 10)]))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            city_idx_val = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': cities[city_idx_val]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))