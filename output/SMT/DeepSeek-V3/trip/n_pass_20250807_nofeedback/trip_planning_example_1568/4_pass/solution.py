from z3 import *

def solve_itinerary():
    # Cities with consistent naming
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 
              'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    
    # Direct flights (undirected)
    direct_flights = [
        ('Riga', 'Stockholm'),
        ('Stockholm', 'Brussels'),
        ('Istanbul', 'Munich'),
        ('Istanbul', 'Riga'),
        ('Prague', 'Split'),
        ('Vienna', 'Brussels'),
        ('Vienna', 'Riga'),
        ('Split', 'Stockholm'),
        ('Munich', 'Amsterdam'),
        ('Split', 'Amsterdam'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Riga'),
        ('Vienna', 'Stockholm'),
        ('Vienna', 'Istanbul'),
        ('Vienna', 'Seville'),
        ('Istanbul', 'Amsterdam'),
        ('Munich', 'Brussels'),
        ('Prague', 'Munich'),
        ('Riga', 'Munich'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Brussels'),
        ('Prague', 'Istanbul'),
        ('Istanbul', 'Stockholm'),
        ('Vienna', 'Prague'),
        ('Munich', 'Split'),
        ('Vienna', 'Amsterdam'),
        ('Prague', 'Stockholm'),
        ('Brussels', 'Seville'),
        ('Munich', 'Stockholm'),
        ('Istanbul', 'Brussels'),
        ('Amsterdam', 'Seville'),
        ('Vienna', 'Split'),
        ('Munich', 'Seville'),
        ('Riga', 'Brussels'),
        ('Prague', 'Riga'),
        ('Vienna', 'Munich')
    ]
    
    # Create flight pairs (undirected)
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Days 1-20
    days = 20
    day_range = range(1, days + 1)
    
    # Z3 variables
    city_vars = {city: Int(city) for city in cities}
    assignments = {day: Int(f'day_{day}') for day in day_range}
    
    # Solver
    s = Solver()
    
    # Each day is assigned to exactly one city
    for day in day_range:
        s.add(Or([assignments[day] == city_vars[city] for city in cities]))
    
    # City stay duration constraints
    # Prague: 5 days (must include days 5-9)
    s.add(Sum([If(assignments[day] == city_vars['Prague'], 1, 0) for day in day_range]) == 5)
    for day in range(5, 10):
        s.add(assignments[day] == city_vars['Prague'])
    
    # Brussels: 2 days
    s.add(Sum([If(assignments[day] == city_vars['Brussels'], 1, 0) for day in day_range]) == 2)
    
    # Riga: 2 days (must include day 15 or 16)
    s.add(Sum([If(assignments[day] == city_vars['Riga'], 1, 0) for day in day_range]) == 2)
    s.add(Or(assignments[15] == city_vars['Riga'], assignments[16] == city_vars['Riga']))
    
    # Munich: 2 days
    s.add(Sum([If(assignments[day] == city_vars['Munich'], 1, 0) for day in day_range]) == 2)
    
    # Seville: 3 days
    s.add(Sum([If(assignments[day] == city_vars['Seville'], 1, 0) for day in day_range]) == 3)
    
    # Stockholm: 2 days (must be days 16-17)
    s.add(Sum([If(assignments[day] == city_vars['Stockholm'], 1, 0) for day in day_range]) == 2)
    s.add(assignments[16] == city_vars['Stockholm'])
    s.add(assignments[17] == city_vars['Stockholm'])
    
    # Istanbul: 2 days
    s.add(Sum([If(assignments[day] == city_vars['Istanbul'], 1, 0) for day in day_range]) == 2)
    
    # Amsterdam: 3 days
    s.add(Sum([If(assignments[day] == city_vars['Amsterdam'], 1, 0) for day in day_range]) == 3)
    
    # Vienna: 5 days (must include at least one day between 1-5)
    s.add(Sum([If(assignments[day] == city_vars['Vienna'], 1, 0) for day in day_range]) == 5)
    s.add(Or([assignments[day] == city_vars['Vienna'] for day in range(1, 6)]))
    
    # Split: 3 days (must include days 11-13)
    s.add(Sum([If(assignments[day] == city_vars['Split'], 1, 0) for day in day_range]) == 3)
    for day in range(11, 14):
        s.add(assignments[day] == city_vars['Split'])
    
    # Flight constraints
    for day in range(1, days):
        current = assignments[day]
        next_day = assignments[day + 1]
        s.add(Implies(current != next_day, 
                     Or([And(current == city_vars[a], next_day == city_vars[b]) 
                        for a, b in flight_pairs])))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_map = {model.eval(city_vars[city]).as_long(): city for city in cities}
        
        current_city = None
        start_day = 1
        for day in day_range:
            city_num = model.eval(assignments[day]).as_long()
            city = city_map[city_num]
            if city != current_city:
                if current_city is not None:
                    itinerary.append({'day': start_day, 'city': current_city})
                current_city = city
                start_day = day
        itinerary.append({'day': start_day, 'city': current_city})
        
        # Group consecutive days in same city
        grouped_itinerary = []
        current = itinerary[0]
        for item in itinerary[1:]:
            if item['city'] == current['city']:
                continue
            else:
                grouped_itinerary.append({
                    'day_range': f"Day {current['day']}-{item['day']-1}",
                    'place': current['city']
                })
                current = item
        grouped_itinerary.append({
            'day_range': f"Day {current['day']}-{days}",
            'place': current['city']
        })
        
        return {'itinerary': grouped_itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Solve and print
itinerary = solve_itinerary()
print(itinerary)