from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flight_pairs = [
        ('Prague', 'Tallinn'), ('Prague', 'Zurich'), ('Florence', 'Prague'),
        ('Frankfurt', 'Bucharest'), ('Frankfurt', 'Venice'), ('Prague', 'Bucharest'),
        ('Bucharest', 'Zurich'), ('Tallinn', 'Frankfurt'), ('Zurich', 'Florence'),
        ('Frankfurt', 'Zurich'), ('Zurich', 'Venice'), ('Florence', 'Frankfurt'),
        ('Prague', 'Frankfurt'), ('Tallinn', 'Zurich')
    ]
    # Create flight connections set
    connections = set()
    for a, b in flight_pairs:
        connections.add((city_map[a], city_map[b]))
        connections.add((city_map[b], city_map[a]))
    
    # Create Z3 solver
    s = Solver()
    
    # Variables for stay segments
    # Each stay has: start_day, end_day, city
    stays = []
    max_stays = 10  # Reasonable upper bound
    
    for i in range(max_stays):
        start = Int(f'stay_{i}_start')
        end = Int(f'stay_{i}_end')
        city = Int(f'stay_{i}_city')
        stays.append((start, end, city))
        # Initial constraints
        s.add(start >= 1, start <= 26)
        s.add(end >= 1, end <= 26)
        s.add(city >= 0, city < len(cities))
        s.add(end >= start)
    
    # Constraints for fixed date ranges
    # Venice: days 22-26
    s.add(Or([And(stay[0] <= 22, stay[1] >= 26, stay[2] == city_map['Venice']) for stay in stays))
    
    # Frankfurt: days 12-16
    s.add(Or([And(stay[0] <= 12, stay[1] >= 16, stay[2] == city_map['Frankfurt']) for stay in stays))
    
    # Tallinn: days 8-12
    s.add(Or([And(stay[0] <= 8, stay[1] >= 12, stay[2] == city_map['Tallinn']) for stay in stays))
    
    # Total days per city
    city_days = [Int(f'days_{city}') for city in cities]
    for i, city in enumerate(cities):
        s.add(city_days[i] == Sum([If(And(stay[2] == i, stay[0] <= d, stay[1] >= d), 1, 0) 
                                 for stay in stays for d in range(1, 27)]))
    
    s.add(city_days[city_map['Bucharest']] == 3)
    s.add(city_days[city_map['Venice']] == 5)
    s.add(city_days[city_map['Prague']] == 4)
    s.add(city_days[city_map['Frankfurt']] == 5)
    s.add(city_days[city_map['Zurich']] == 5)
    s.add(city_days[city_map['Florence']] == 5)
    s.add(city_days[city_map['Tallinn']] == 5)
    
    # Flight connections between stays
    for i in range(max_stays - 1):
        for j in range(i + 1, max_stays):
            s.add(Implies(
                And(stays[i][1] + 1 == stays[j][0], stays[i][2] != stays[j][2]),
                Or([And(stays[i][2] == a, stays[j][2] == b) for a, b in connections])
            ))
    
    # No overlapping stays
    for i in range(max_stays):
        for j in range(i + 1, max_stays):
            s.add(Or(
                stays[i][1] < stays[j][0],
                stays[j][1] < stays[i][0]
            ))
    
    # Cover all days
    for d in range(1, 27):
        s.add(Or([And(stay[0] <= d, stay[1] >= d) for stay in stays]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Collect all stays
        active_stays = []
        for stay in stays:
            start = m.evaluate(stay[0]).as_long()
            end = m.evaluate(stay[1]).as_long()
            city_idx = m.evaluate(stay[2]).as_long()
            if start <= end:  # Valid stay
                active_stays.append((start, end, cities[city_idx]))
        
        # Sort by start day
        active_stays.sort()
        
        # Build itinerary
        for day in range(1, 27):
            for stay in active_stays:
                if stay[0] <= day <= stay[1]:
                    itinerary.append({'day': day, 'city': stay[2]})
                    break
        
        # Verify all days are covered
        if len(itinerary) != 26:
            return None
        
        return {'itinerary': itinerary}
    else:
        return None

# Solve and print
result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")