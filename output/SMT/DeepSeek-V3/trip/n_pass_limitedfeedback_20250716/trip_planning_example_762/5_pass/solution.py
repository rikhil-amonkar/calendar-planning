from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('London', 'Madrid'),
        ('Oslo', 'Vilnius'),
        ('Berlin', 'Vilnius'),
        ('Madrid', 'Oslo'),
        ('Madrid', 'Dublin'),
        ('London', 'Oslo'),
        ('Madrid', 'Berlin'),
        ('Berlin', 'Oslo'),
        ('Dublin', 'Oslo'),
        ('London', 'Dublin'),
        ('London', 'Berlin'),
        ('Berlin', 'Dublin')
    ]
    
    # Create allowed transitions
    allowed = set()
    for a, b in direct_flights:
        allowed.add((city_map[a], city_map[b]))
        allowed.add((city_map[b], city_map[a]))
    
    # Create solver and variables
    s = Solver()
    days = 13
    itinerary = [Int(f'day_{i}') for i in range(days)]
    
    # Each day must be a valid city
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    # Transition constraints
    for i in range(days - 1):
        current = itinerary[i]
        next_day = itinerary[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current != next_day, (current, next_day) in allowed)  # Fly to connected city
        ))
    
    # Total days per city (including flight days)
    total_days = {city: 0 for city in cities}
    for city in cities:
        total_days[city] = Sum([If(itinerary[i] == city_map[city], 1, 0) for i in range(days)])
    
    s.add(total_days['Dublin'] == 3)
    s.add(total_days['Madrid'] == 2)
    s.add(total_days['Oslo'] == 3)
    s.add(total_days['London'] == 2)
    s.add(total_days['Vilnius'] == 3)
    s.add(total_days['Berlin'] == 5)
    
    # Specific day constraints
    # Dublin between day 7-9 (1-based)
    s.add(Or(
        itinerary[6] == city_map['Dublin'],  # day 7
        itinerary[7] == city_map['Dublin'],  # day 8
        itinerary[8] == city_map['Dublin']   # day 9
    ))
    
    # Madrid between day 2-3 (1-based)
    s.add(Or(
        itinerary[1] == city_map['Madrid'],  # day 2
        itinerary[2] == city_map['Madrid']   # day 3
    ))
    
    # Berlin between day 3-7 (1-based)
    s.add(Or(
        itinerary[2] == city_map['Berlin'],  # day 3
        itinerary[3] == city_map['Berlin'],  # day 4
        itinerary[4] == city_map['Berlin'],  # day 5
        itinerary[5] == city_map['Berlin'],  # day 6
        itinerary[6] == city_map['Berlin']   # day 7
    ))
    
    # Additional constraints to guide the solver
    # Start in Madrid (common starting point)
    s.add(itinerary[0] == city_map['Madrid'])
    
    # Ensure we don't have long single-city stays that would prevent meeting other constraints
    for i in range(days - 3):
        s.add(Not(And(
            itinerary[i] == itinerary[i+1],
            itinerary[i] == itinerary[i+2],
            itinerary[i] == itinerary[i+3]
        )))
    
    # Check solution
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(days):
            city_idx = model.evaluate(itinerary[i]).as_long()
            result.append({'day': i+1, 'place': cities[city_idx]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in result:
            counts[entry['place']] += 1
        
        # Verify transitions
        valid = True
        for i in range(days - 1):
            current = city_map[result[i]['place']]
            next_place = city_map[result[i+1]['place']]
            if current != next_place and (current, next_place) not in allowed:
                valid = False
                break
        
        required_days = {
            'Dublin': 3,
            'Madrid': 2,
            'Oslo': 3,
            'London': 2,
            'Vilnius': 3,
            'Berlin': 5
        }
        
        if valid and all(counts[city] == required_days[city] for city in cities):
            return {'itinerary': result}
        else:
            print("Solution found but doesn't meet all constraints")
            return None
    else:
        print("No solution found")
        return None

solution = solve_itinerary()
if solution:
    print(solution)
else:
    print("No valid itinerary found")