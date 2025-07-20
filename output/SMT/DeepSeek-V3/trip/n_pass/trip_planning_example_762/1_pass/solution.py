from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: bidirectional
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
    
    # Create a set of allowed transitions (bidirectional)
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((city_map[a], city_map[b]))
        allowed_transitions.add((city_map[b], city_map[a]))
    
    # Create Z3 variables: day 1 to day 13, each is a city (0 to 5)
    s = Solver()
    days = 13
    itinerary = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Each day must be a valid city (0 to 5)
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    # Transition constraints: consecutive days must be the same or connected by direct flight
    for i in range(days - 1):
        current = itinerary[i]
        next_day = itinerary[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current == next_day,
            And(current != next_day, (current, next_day) in allowed_transitions)
        ))
    
    # Total days per city constraints
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
    # Dublin between day 7 and day 9 (inclusive, 1-based)
    s.add(Or(
        itinerary[6] == city_map['Dublin'],  # day 7
        itinerary[7] == city_map['Dublin'],  # day 8
        itinerary[8] == city_map['Dublin']   # day 9
    ))
    
    # Madrid between day 2 and day 3 (1-based)
    s.add(Or(
        itinerary[1] == city_map['Madrid'],  # day 2
        itinerary[2] == city_map['Madrid']   # day 3
    ))
    
    # Berlin between day 3 and day 7 (1-based)
    s.add(Or(
        itinerary[2] == city_map['Berlin'],  # day 3
        itinerary[3] == city_map['Berlin'],  # day 4
        itinerary[4] == city_map['Berlin'],  # day 5
        itinerary[5] == city_map['Berlin'],  # day 6
        itinerary[6] == city_map['Berlin']   # day 7
    ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(days):
            city_idx = model.evaluate(itinerary[i]).as_long()
            result.append({'day': i + 1, 'place': cities[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in result:
            counts[entry['place']] += 1
        
        # Verify transitions
        valid = True
        for i in range(days - 1):
            current = city_map[result[i]['place']]
            next_place = city_map[result[i + 1]['place']]
            if current != next_place and (current, next_place) not in allowed_transitions:
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
            print("Generated itinerary does not meet all constraints.")
            return None
    else:
        print("No solution found.")
        return None

solution = solve_itinerary()
if solution:
    print(solution)
else:
    print("No valid itinerary found.")