from z3 import *

def solve_itinerary():
    # Cities with their required days
    cities = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    city_names = list(cities.keys())
    city_map = {city: idx for idx, city in enumerate(city_names)}
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ('Helsinki', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Riga'),
        ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'),
        ('Tallinn', 'Dublin'),
        ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Vienna', 'Dublin')
    ]
    
    # Create flight graph
    flight_graph = {city: set() for city in city_names}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Initialize solver
    s = Solver()
    
    # Day variables (1-15)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    for day in days:
        s.add(day >= 0, day < len(city_names))
    
    # Total days constraints
    for city, req_days in cities.items():
        city_idx = city_map[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in days]) == req_days)
    
    # Specific event constraints
    # Vienna show on day 2 or 3
    vienna_idx = city_map['Vienna']
    s.add(Or(days[1] == vienna_idx, days[2] == vienna_idx))
    
    # Helsinki friends between days 3-5
    helsinki_idx = city_map['Helsinki']
    s.add(Or([days[i] == helsinki_idx for i in [2, 3, 4]]))
    
    # Tallinn wedding between days 7-11
    tallinn_idx = city_map['Tallinn']
    s.add(Or([days[i] == tallinn_idx for i in range(6, 11)]))
    
    # Flight connectivity constraints
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or move to connected city
        s.add(Or(
            current == next_day,
            *[And(current == city_map[a], next_day == city_map[b]) 
              for a, b in direct_flights]
        ))
    
    # Solve and format output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day_num in range(1, 16):
            city_idx = model.evaluate(days[day_num-1]).as_long()
            itinerary.append({
                'day': day_num,
                'place': city_names[city_idx]
            })
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))