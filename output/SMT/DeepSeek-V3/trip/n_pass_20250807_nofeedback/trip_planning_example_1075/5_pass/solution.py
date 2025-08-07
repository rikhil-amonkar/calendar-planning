from z3 import *

def solve_itinerary():
    # Cities with their indices
    cities = ['Vienna', 'Lyon', 'Edinburgh', 'Reykjavik', 'Stuttgart', 'Manchester', 'Split', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flight_pairs = [
        ('Reykjavik', 'Stuttgart'), ('Reykjavik', 'Vienna'),
        ('Stuttgart', 'Split'), ('Stuttgart', 'Vienna'), ('Stuttgart', 'Edinburgh'), ('Stuttgart', 'Manchester'),
        ('Prague', 'Manchester'), ('Prague', 'Edinburgh'), ('Prague', 'Vienna'), ('Prague', 'Split'), ('Prague', 'Lyon'), ('Prague', 'Reykjavik'),
        ('Edinburgh', 'Prague'), ('Edinburgh', 'Stuttgart'),
        ('Manchester', 'Split'), ('Manchester', 'Prague'), ('Manchester', 'Vienna'),
        ('Vienna', 'Manchester'), ('Vienna', 'Lyon'), ('Vienna', 'Split'), ('Vienna', 'Prague'), ('Vienna', 'Stuttgart'), ('Vienna', 'Reykjavik'),
        ('Split', 'Lyon'), ('Split', 'Manchester'), ('Split', 'Prague'), ('Split', 'Vienna'), ('Split', 'Stuttgart'),
        ('Lyon', 'Vienna'), ('Lyon', 'Split'), ('Lyon', 'Prague')
    ]
    
    # Create adjacency matrix
    adj = [[False]*len(cities) for _ in cities]
    for city1, city2 in flight_pairs:
        i, j = city_map[city1], city_map[city2]
        adj[i][j] = adj[j][i] = True
    
    # Required days per city
    required_days = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    # Initialize solver
    s = Solver()
    
    # Day variables (1-25)
    days = [Int(f'day_{i}') for i in range(1, 26)]
    
    # Each day must be a valid city
    for day in days:
        s.add(And(day >= 0, day < len(cities)))
    
    # Fixed stays
    for i in range(5, 9):  # Edinburgh days 5-8
        s.add(days[i-1] == city_map['Edinburgh'])
    for i in range(19, 24):  # Split days 19-23
        s.add(days[i-1] == city_map['Split'])
    
    # Flight transitions
    for i in range(1, 25):
        current = days[i-1]
        next_day = days[i]
        # Either stay or take a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == city_map[c1], next_day == city_map[c2]) 
             for c1, c2 in flight_pairs if c1 != c2]
        ))
    
    # Duration constraints
    for city, req in required_days.items():
        idx = city_map[city]
        s.add(Sum([If(d == idx, 1, 0) for d in days]) == req)
    
    # Additional constraints to help the solver
    # Start in Reykjavik (since it's isolated)
    s.add(days[0] == city_map['Reykjavik'])
    # End in Split (since wedding is at the end)
    s.add(days[24] == city_map['Split'])
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 26):
            city_idx = m.evaluate(days[i-1]).as_long()
            itinerary.append({'day': i, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return None

itinerary = solve_itinerary()
if itinerary:
    print(itinerary)
else:
    print("No valid itinerary found.")