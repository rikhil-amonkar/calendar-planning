from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Riga': 4,
        'Manchester': 5,
        'Bucharest': 4,
        'Florence': 4,
        'Vienna': 2,
        'Istanbul': 2,
        'Reykjavik': 4,
        'Stuttgart': 5
    }
    city_names = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_names)}
    
    # Corrected direct flights (bidirectional)
    direct_flights = [
        ('Bucharest', 'Vienna'),
        ('Bucharest', 'Riga'),
        ('Bucharest', 'Istanbul'),
        ('Bucharest', 'Manchester'),
        ('Reykjavik', 'Vienna'),
        ('Reykjavik', 'Stuttgart'),
        ('Manchester', 'Vienna'),
        ('Manchester', 'Riga'),
        ('Manchester', 'Istanbul'),
        ('Manchester', 'Stuttgart'),
        ('Riga', 'Vienna'),
        ('Riga', 'Istanbul'),
        ('Istanbul', 'Vienna'),
        ('Istanbul', 'Stuttgart'),
        ('Vienna', 'Florence'),
        ('Vienna', 'Stuttgart'),
        ('Stuttgart', 'Reykjavik')
    ]
    
    # Create flight connections graph
    flight_graph = {i: [] for i in range(len(city_names))}
    for city1, city2 in direct_flights:
        idx1 = city_to_idx[city1]
        idx2 = city_to_idx[city2]
        flight_graph[idx1].append(idx2)
        flight_graph[idx2].append(idx1)
    
    # Days: 1 to 23 (1-based)
    num_days = 23
    days = range(1, num_days + 1)
    
    # Create Z3 variables
    day_vars = [Int(f'day_{day}') for day in days]
    s = Solver()
    
    # Each day variable must be a valid city index
    for day_var in day_vars:
        s.add(And(day_var >= 0, day_var < len(city_names)))
    
    # Flight constraints between consecutive days
    for i in range(num_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([next_day == flight for flight in flight_graph[current]])  # Or take direct flight
        ))
    
    # Duration constraints
    for city, required_days in cities.items():
        idx = city_to_idx[city]
        days_in_city = Sum([If(day_var == idx, 1, 0) for day_var in day_vars])
        s.add(days_in_city == required_days)
    
    # Special constraints
    # Bucharest workshop between days 16-19 (must be there at least one day)
    bucharest_idx = city_to_idx['Bucharest']
    s.add(Or([day_vars[i] == bucharest_idx for i in range(15, 19)]))  # days 16-19
    
    # Istanbul show on days 12-13 (must be there at least one day)
    istanbul_idx = city_to_idx['Istanbul']
    s.add(Or(day_vars[11] == istanbul_idx, day_vars[12] == istanbul_idx))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in days:
            city_idx = model.evaluate(day_vars[day - 1]).as_long()
            itinerary.append({'day': day, 'place': city_names[city_idx]})
        
        # Verify days count
        counts = {city: 0 for city in city_names}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        return {'itinerary': itinerary, 'counts': counts}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(result)