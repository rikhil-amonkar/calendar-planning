from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Porto', 'Oslo'),
        ('Edinburgh', 'Budapest'),
        ('Edinburgh', 'Geneva'),
        ('Riga', 'Tallinn'),
        ('Edinburgh', 'Porto'),
        ('Vilnius', 'Helsinki'),
        ('Tallinn', 'Vilnius'),
        ('Riga', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Edinburgh', 'Oslo'),
        ('Edinburgh', 'Helsinki'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Helsinki'),
        ('Budapest', 'Geneva'),
        ('Helsinki', 'Budapest'),
        ('Helsinki', 'Oslo'),
        ('Edinburgh', 'Riga'),
        ('Tallinn', 'Helsinki'),
        ('Geneva', 'Porto'),
        ('Budapest', 'Oslo'),
        ('Helsinki', 'Geneva'),
        ('Riga', 'Vilnius'),
        ('Tallinn', 'Oslo')
    ]
    
    # Create flight connections (both directions)
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Required days in each city
    required_days = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Initialize Z3 solver
    s = Solver()
    
    # Variables: day 1 to 25, each is a city index (0-8)
    days = [Int(f'day_{i}') for i in range(1, 26)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Constraint 1: Total days per city must match required_days
    for city in cities:
        city_idx = city_to_idx[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in days]) == required_days[city])
    
    # Constraint 2: Transitions must be via direct flights
    for i in range(len(days) - 1):
        current_day = days[i]
        next_day = days[i + 1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current_day == next_day,
            *[
                And(current_day == city_to_idx[a], next_day == city_to_idx[b])
                for a, b in flight_pairs
            ]
        ))
    
    # Constraint 3: Wedding in Tallinn between days 4-8
    tallinn_idx = city_to_idx['Tallinn']
    s.add(Or(*[days[i] == tallinn_idx for i in range(3, 8)]))  # days 4-8 (1-based)
    
    # Constraint 4: Meet in Oslo between days 24-25
    oslo_idx = city_to_idx['Oslo']
    s.add(Or(days[23] == oslo_idx, days[24] == oslo_idx))  # days 24-25 (1-based)
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 26):
            city_idx = model.evaluate(days[i-1]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': i, 'city': city})
        
        # Verify all constraints are satisfied
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['city']] += 1
        
        for city in cities:
            if city_counts[city] != required_days[city]:
                return {'error': f"Day count mismatch for {city}"}
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['city']
            next_c = itinerary[i+1]['city']
            if current != next_c and (current, next_c) not in flight_pairs:
                return {'error': f"Invalid flight from {current} to {next_c}"}
        
        tallinn_days = [e['day'] for e in itinerary if e['city'] == 'Tallinn']
        if not any(4 <= d <= 8 for d in tallinn_days):
            return {'error': "Wedding constraint not satisfied"}
        
        oslo_days = [e['day'] for e in itinerary if e['city'] == 'Oslo']
        if not any(d == 24 or d == 25 for d in oslo_days):
            return {'error': "Meeting constraint not satisfied"}
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

# Execute and print the result
result = solve_itinerary()
print(result)