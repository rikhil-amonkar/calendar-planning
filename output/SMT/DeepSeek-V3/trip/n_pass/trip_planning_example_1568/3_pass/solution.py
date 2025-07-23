from z3 import *

def solve_itinerary():
    # Cities involved
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (city1, city2)
    direct_flights = [
        ('Riga', 'Stockholm'), ('Stockholm', 'Brussels'), ('Istanbul', 'Munich'), ('Istanbul', 'Riga'),
        ('Prague', 'Split'), ('Vienna', 'Brussels'), ('Vienna', 'Riga'), ('Split', 'Stockholm'),
        ('Munich', 'Amsterdam'), ('Split', 'Amsterdam'), ('Amsterdam', 'Stockholm'), ('Amsterdam', 'Riga'),
        ('Vienna', 'Stockholm'), ('Vienna', 'Istanbul'), ('Vienna', 'Seville'), ('Istanbul', 'Amsterdam'),
        ('Munich', 'Brussels'), ('Prague', 'Munich'), ('Riga', 'Munich'), ('Prague', 'Amsterdam'),
        ('Prague', 'Brussels'), ('Prague', 'Istanbul'), ('Vienna', 'Prague'), ('Munich', 'Split'),
        ('Vienna', 'Amsterdam'), ('Prague', 'Stockholm'), ('Brussels', 'Seville'), ('Munich', 'Stockholm'),
        ('Istanbul', 'Brussels'), ('Amsterdam', 'Seville'), ('Vienna', 'Split'), ('Munich', 'Seville'),
        ('Riga', 'Brussels'), ('Prague', 'Riga'), ('Vienna', 'Munich')
    ]
    # Normalize flight connections to include both directions
    normalized_flights = set()
    for city1, city2 in direct_flights:
        if city1 in city_to_int and city2 in city_to_int:
            normalized_flights.add((city1, city2))
            normalized_flights.add((city2, city1))
    
    # Create adjacency list for direct flights
    adjacency = {i: set() for i in range(len(cities))}
    for city1, city2 in normalized_flights:
        i1 = city_to_int[city1]
        i2 = city_to_int[city2]
        adjacency[i1].add(i2)
        adjacency[i2].add(i1)
    
    # Z3 solver setup
    s = Solver()
    
    # Variables: day 1 to 20, each is an integer representing a city
    day_vars = [Int(f'day_{i}') for i in range(1, 21)]
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for consecutive days: adjacent cities or same city
    for i in range(19):
        current_day = day_vars[i]
        next_day = day_vars[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            And(current_day != next_day, Or([next_day == j for j in adjacency[model.evaluate(current_day).as_long()]]))
        ))
    
    # City stay durations
    total_days = {
        'Prague': 5,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Stockholm': 2,
        'Istanbul': 2,
        'Amsterdam': 3,
        'Vienna': 5,
        'Split': 3
    }
    
    # Constraints for total days per city
    for city, total in total_days.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in day_vars]) == total)
    
    # Specific constraints:
    # Prague: 5 days, including day 5-9 for the show (indices 4-8 in 0-based)
    prague_idx = city_to_int['Prague']
    s.add(And([day_vars[i] == prague_idx for i in range(4, 9)]))
    
    # Riga: 2 days, including meeting friends between day 15-16 (indices 14-15)
    riga_idx = city_to_int['Riga']
    s.add(Or(day_vars[14] == riga_idx, day_vars[15] == riga_idx))
    
    # Stockholm: conference during day 16-17 (indices 15-16)
    stockholm_idx = city_to_int['Stockholm']
    s.add(Or(day_vars[15] == stockholm_idx, day_vars[16] == stockholm_idx))
    
    # Vienna: meet friend between day 1-5 (indices 0-4)
    vienna_idx = city_to_int['Vienna']
    s.add(Or([day_vars[i] == vienna_idx for i in range(5)]))
    
    # Split: visit relatives between day 11-13 (indices 10-12)
    split_idx = city_to_int['Split']
    s.add(Or([day_vars[i] == split_idx for i in range(10, 13)]))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            day_num = i + 1
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))