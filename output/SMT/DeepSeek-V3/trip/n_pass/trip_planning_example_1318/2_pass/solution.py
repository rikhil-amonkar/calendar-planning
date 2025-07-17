from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected unless specified)
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
    
    # Create a set of bidirectional flight connections
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
    
    # Special constraints:
    # - Wedding in Tallinn between day 4 and 8 (inclusive). So at least one day in Tallinn must be in 4-8.
    # - Meet friend in Oslo between day 24 and 25. So Oslo must include day 24 or 25.
    
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
    
    # Constraint 2: Transitions between cities must be direct flights
    for i in range(len(days) - 1):
        current_day_city = days[i]
        next_day_city = days[i + 1]
        # The transition is allowed if current_day_city == next_day_city or there's a flight between them
        s.add(Or(
            current_day_city == next_day_city,
            *[
                And(current_day_city == city_to_idx[a], next_day_city == city_to_idx[b])
                for a, b in flight_pairs
            ]
        ))
    
    # Constraint 3: Wedding in Tallinn between day 4 and 8 (1-based days are 3 to 7 in zero-based?)
    # At least one day in Tallinn must be between days 4-8 (1-based)
    tallinn_idx = city_to_idx['Tallinn']
    s.add(Or(*[days[i] == tallinn_idx for i in range(3, 8)]))  # days 4-8 (1-based) are indices 3-7
    
    # Constraint 4: Meet friend in Oslo between day 24-25 (1-based days 24 and 25 are indices 23 and 24)
    oslo_idx = city_to_idx['Oslo']
    s.add(Or(days[23] == oslo_idx, days[24] == oslo_idx))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 26):
            city_idx = model.evaluate(days[i-1]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': i, 'city': city})
        
        # Verify the solution meets all constraints
        # Check days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['city']] += 1
        for city in cities:
            assert city_days[city] == required_days[city], f"City {city} has {city_days[city]} days instead of {required_days[city]}"
        
        # Check transitions are valid flights
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if current_city != next_city:
                assert (current_city, next_city) in flight_pairs, f"No flight from {current_city} to {next_city}"
        
        # Check wedding in Tallinn between days 4-8
        tallinn_days = [entry['day'] for entry in itinerary if entry['city'] == 'Tallinn']
        assert any(4 <= day <= 8 for day in tallinn_days), "Tallinn wedding days not met"
        
        # Check Oslo meeting between days 24-25
        oslo_days = [entry['day'] for entry in itinerary if entry['city'] == 'Oslo']
        assert any(day == 24 or day == 25 for day in oslo_days), "Oslo meeting days not met"
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

# Execute and print the result
result = solve_itinerary()
print(result)