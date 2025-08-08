from z3 import *
import json

def solve_itinerary():
    # Define cities and their indices
    cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
    city_idx = {c: i for i, c in enumerate(cities)}
    
    # Define direct flight connections (bidirectional)
    connections = [
        ('Zurich', 'Helsinki'),
        ('Hamburg', 'Bucharest'),
        ('Helsinki', 'Hamburg'),
        ('Zurich', 'Hamburg'),
        ('Zurich', 'Bucharest'),
        ('Zurich', 'Split'),
        ('Helsinki', 'Split'),
        ('Split', 'Hamburg')
    ]
    
    # Create flight graph (undirected)
    flight_graph = {c: set() for c in cities}
    for a, b in connections:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    days = 12
    s = Solver()
    
    # Create variables for each day's location
    loc = [Int(f'day_{i}') for i in range(days)]
    for day in loc:
        s.add(day >= 0, day < len(cities))
    
    # City day count constraints
    s.add(Sum([If(loc[i] == city_idx['Hamburg'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(loc[i] == city_idx['Zurich'], 1, 0) for i in range(days)]) == 3)
    s.add(Sum([If(loc[i] == city_idx['Helsinki'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(loc[i] == city_idx['Bucharest'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(loc[i] == city_idx['Split'], 1, 0) for i in range(days)]) == 7)
    
    # Conference days in Split (day 4 and 10, 1-based)
    s.add(loc[3] == city_idx['Split'])  # Day 4
    s.add(loc[9] == city_idx['Split'])  # Day 10
    
    # Wedding in Zurich between day 1-3
    s.add(Or([loc[i] == city_idx['Zurich'] for i in range(3)]))
    
    # Flight constraints between consecutive days
    for i in range(days - 1):
        current = loc[i]
        next_ = loc[i + 1]
        # Either stay or fly to connected city
        s.add(Or(
            current == next_,
            *[And(current == city_idx[a], next_ == city_idx[b]) 
              for a in flight_graph for b in flight_graph[a]]
        ))
    
    # Additional constraints to help find solution:
    # 1. Don't make too many flights (limit to 4 flights)
    # 2. Ensure reasonable stays in cities
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city = cities[m.evaluate(loc[i]).as_long()]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify all constraints are met
        city_days = {c: 0 for c in cities}
        for day in itinerary:
            city_days[day['place']] += 1
        
        assert city_days['Hamburg'] == 2
        assert city_days['Zurich'] == 3
        assert city_days['Helsinki'] == 2
        assert city_days['Bucharest'] == 2
        assert city_days['Split'] == 7
        assert itinerary[3]['place'] == 'Split'  # Day 4
        assert itinerary[9]['place'] == 'Split'  # Day 10
        assert any(day['place'] == 'Zurich' for day in itinerary[:3])  # Wedding
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))