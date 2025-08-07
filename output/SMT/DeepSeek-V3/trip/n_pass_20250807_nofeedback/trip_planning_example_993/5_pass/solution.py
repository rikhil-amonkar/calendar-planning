from z3 import *

def solve_itinerary():
    # Cities with their indices
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('London', 'Amsterdam'),
        ('Vilnius', 'Frankfurt'),
        ('Riga', 'Vilnius'),
        ('Riga', 'Stockholm'),
        ('London', 'Bucharest'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Bucharest', 'Riga'),
        ('Amsterdam', 'Riga'),
        ('Amsterdam', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Bucharest', 'Frankfurt'),
        ('London', 'Frankfurt'),
        ('London', 'Stockholm'),
        ('Amsterdam', 'Vilnius')
    ]
    
    # Create adjacency matrix
    adjacency = [[False]*len(cities) for _ in range(len(cities))]
    for a, b in direct_flights:
        i, j = city_map[a], city_map[b]
        adjacency[i][j] = True
        adjacency[j][i] = True
    
    # Z3 variables: day[i] is city index on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    s = Solver()
    
    # Each day must be a valid city index
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Day count constraints
    day_counts = [
        ('Riga', 2),
        ('Frankfurt', 3),
        ('Amsterdam', 2),
        ('Vilnius', 5),
        ('London', 2),
        ('Stockholm', 3),
        ('Bucharest', 4)
    ]
    
    for city, count in day_counts:
        s.add(Sum([If(d == city_map[city], 1, 0) for d in days]) == count)
    
    # Special constraints
    # Amsterdam visit between day 2-3
    s.add(Or(days[1] == city_map['Amsterdam'], days[2] == city_map['Amsterdam']))
    
    # Vilnius workshop between day 7-11
    s.add(Or([days[i] == city_map['Vilnius'] for i in range(6, 11)]))
    
    # Stockholm wedding between day 13-15
    s.add(Or([days[i] == city_map['Stockholm'] for i in range(12, 15)]))
    
    # Flight constraints
    for i in range(14):  # Check transitions between days
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or have a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) 
              for a in range(len(cities)) 
              for b in range(len(cities)) 
              if adjacency[a][b]]
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day_num in range(1, 16):
            city_idx = model.evaluate(days[day_num-1]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the solution meets all constraints
        return {'itinerary': itinerary}
    else:
        print("No valid itinerary found")
        return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))