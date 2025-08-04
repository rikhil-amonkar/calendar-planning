from z3 import *

def solve_itinerary():
    # Cities involved
    cities = ['Lyon', 'Paris', 'Riga', 'Berlin', 'Stockholm', 'Zurich', 'Nice', 'Seville', 'Milan', 'Naples']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Paris', 'Stockholm'), ('Seville', 'Paris'), ('Naples', 'Zurich'), ('Nice', 'Riga'),
        ('Berlin', 'Milan'), ('Paris', 'Zurich'), ('Paris', 'Nice'), ('Milan', 'Paris'),
        ('Milan', 'Riga'), ('Paris', 'Lyon'), ('Milan', 'Naples'), ('Paris', 'Riga'),
        ('Berlin', 'Stockholm'), ('Stockholm', 'Riga'), ('Nice', 'Zurich'), ('Milan', 'Zurich'),
        ('Lyon', 'Nice'), ('Zurich', 'Stockholm'), ('Zurich', 'Riga'), ('Berlin', 'Naples'),
        ('Milan', 'Stockholm'), ('Berlin', 'Zurich'), ('Milan', 'Seville'), ('Paris', 'Naples'),
        ('Berlin', 'Riga'), ('Nice', 'Stockholm'), ('Berlin', 'Paris'), ('Nice', 'Naples'),
        ('Berlin', 'Nice')
    ]
    
    # Create flight connections (both directions)
    flight_connections = {}
    for city in cities:
        flight_connections[city] = set()
    for a, b in direct_flights:
        flight_connections[a].add(b)
        flight_connections[b].add(a)
    
    # Z3 solver
    s = Solver()
    
    # Variables: day_1 to day_23, each representing a city index
    days = [Int(f'day_{i}') for i in range(1, 24)]
    
    # Each day must be a valid city index
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints
    # Berlin: wedding on days 1-2
    s.add(days[0] == city_map['Berlin'])
    s.add(days[1] == city_map['Berlin'])
    
    # Stockholm: annual show on days 20-22
    s.add(days[19] == city_map['Stockholm'])
    s.add(days[20] == city_map['Stockholm'])
    s.add(days[21] == city_map['Stockholm'])
    
    # Nice: workshop on days 12-13
    s.add(days[11] == city_map['Nice'])
    s.add(days[12] == city_map['Nice'])
    
    # Transition constraints: consecutive days must be same city or connected by flight
    for i in range(len(days)-1):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in same city or fly to connected city
        same_city = (current_city == next_city)
        flight_options = []
        for city in cities:
            if city_map[city] == current_city:
                for neighbor in flight_connections[city]:
                    flight_options.append(next_city == city_map[neighbor])
        s.add(Or(same_city, *flight_options))
    
    # Duration constraints
    required_days = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    for city, req in required_days.items():
        count = Sum([If(days[i] == city_map[city], 1, 0) for i in range(23)])
        s.add(count == req)
    
    # Additional constraints to help the solver
    # No single-day visits except for transitions
    for i in range(1, 22):
        s.add(Or(
            days[i] == days[i-1],
            days[i] == days[i+1],
            And(days[i] != days[i-1], days[i] != days[i+1])
        ))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(23):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))