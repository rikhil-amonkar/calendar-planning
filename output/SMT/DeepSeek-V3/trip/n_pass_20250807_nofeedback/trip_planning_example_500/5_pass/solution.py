from z3 import *

def solve_itinerary():
    # Cities with their IDs
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    city_ids = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}

    # Flight connections (bidirectional unless specified)
    # Manchester to Split is one-way (Manchester → Split)
    flight_connections = [
        ('Hamburg', 'Munich'),
        ('Hamburg', 'Manchester'),
        ('Hamburg', 'Split'),
        ('Munich', 'Split'),
        ('Munich', 'Manchester'),
        ('Munich', 'Lyon'),
        ('Split', 'Lyon'),
        ('Manchester', 'Split')  # One-way
    ]

    # Create solver
    s = Solver()

    # Day variables (1-20)
    days = 20
    day_city = [Int(f'day_{i}') for i in range(1, days+1)]

    # Each day must be one of the cities
    for day in day_city:
        s.add(Or([day == city_ids[city] for city in cities]))

    # Fixed constraints
    s.add(day_city[18] == city_ids['Manchester'])  # Day 19
    s.add(day_city[19] == city_ids['Manchester'])  # Day 20
    s.add(day_city[12] == city_ids['Lyon'])       # Day 13
    s.add(day_city[13] == city_ids['Lyon'])       # Day 14

    # Flight transition constraints
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        
        # Can stay in same city
        same_city = current == next_day
        
        # Or take a valid flight
        valid_flights = []
        for (src, dst) in flight_connections:
            valid_flights.append(And(current == city_ids[src], next_day == city_ids[dst]))
            # Add reverse if bidirectional (except Manchester→Split)
            if (dst, src) not in flight_connections and (dst, src) != ('Split', 'Manchester'):
                valid_flights.append(And(current == city_ids[dst], next_day == city_ids[src]))
        
        s.add(Or(same_city, *valid_flights))

    # Duration constraints
    duration = {
        'Hamburg': 7,
        'Munich': 6,
        'Manchester': 2,
        'Lyon': 2,
        'Split': 7
    }
    
    for city, days_needed in duration.items():
        total = 0
        for day in day_city:
            total += If(day == city_ids[city], 1, 0)
        s.add(total == days_needed)

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_idx = m.evaluate(day_city[i]).as_long()
            city_name = idx_to_city[city_idx]
            itinerary.append({'day': day_num, 'city': city_name})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(result)