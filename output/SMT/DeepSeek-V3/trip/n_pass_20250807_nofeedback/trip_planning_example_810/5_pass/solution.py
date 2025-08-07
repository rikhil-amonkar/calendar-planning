import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Berlin': 3,
        'Nice': 5,
        'Athens': 5,
        'Stockholm': 5,
        'Barcelona': 2,
        'Vilnius': 4,
        'Lyon': 2
    }
    city_list = list(cities.keys())
    num_days = 20
    
    # Direct flights: adjacency list
    direct_flights = {
        'Lyon': ['Nice', 'Barcelona'],
        'Nice': ['Lyon', 'Athens', 'Berlin', 'Barcelona', 'Stockholm'],
        'Athens': ['Stockholm', 'Nice', 'Berlin', 'Vilnius', 'Barcelona'],
        'Stockholm': ['Athens', 'Berlin', 'Nice', 'Barcelona'],
        'Berlin': ['Athens', 'Nice', 'Barcelona', 'Vilnius', 'Stockholm'],
        'Barcelona': ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Lyon'],
        'Vilnius': ['Berlin', 'Athens'],
    }
    
    # Create Z3 solver
    s = Solver()
    
    # Decision variables: city for each day
    day_city = [Int(f'day_{i}') for i in range(num_days)]
    
    # Each day must be assigned to a valid city
    for day in day_city:
        s.add(day >= 0, day < len(city_list))
    
    # Berlin must be on days 1 and 3 (0-based days 0 and 2)
    s.add(day_city[0] == city_list.index('Berlin'))
    s.add(day_city[2] == city_list.index('Berlin'))
    
    # Barcelona workshop between day 3 and 4 (0-based days 2 and 3)
    barcelona_idx = city_list.index('Barcelona')
    s.add(Or(
        day_city[2] == barcelona_idx,
        day_city[3] == barcelona_idx
    ))
    
    # Lyon wedding between day 4 and 5 (0-based days 3 and 4)
    lyon_idx = city_list.index('Lyon')
    s.add(Or(
        day_city[3] == lyon_idx,
        day_city[4] == lyon_idx
    ))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(num_days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        # Either stay in same city or fly to connected city
        same_city = (current == next_day)
        flight_options = []
        for src in direct_flights:
            src_idx = city_list.index(src)
            for dst in direct_flights[src]:
                dst_idx = city_list.index(dst)
                flight_options.append(And(current == src_idx, next_day == dst_idx))
        s.add(Or(same_city, *flight_options))
    
    # Count days in each city (including flight days)
    for city, req_days in cities.items():
        city_idx = city_list.index(city)
        count = Sum([If(day_city[i] == city_idx, 1, 0) for i in range(num_days)])
        s.add(count == req_days)
    
    # Additional constraints to help the solver
    # No single-day visits except for flights
    for i in range(1, num_days - 1):
        s.add(Or(
            day_city[i - 1] == day_city[i],
            day_city[i] == day_city[i + 1]
        ))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(num_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({
                'day': day + 1,  # Convert to 1-based
                'place': city_list[city_idx]
            })
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())