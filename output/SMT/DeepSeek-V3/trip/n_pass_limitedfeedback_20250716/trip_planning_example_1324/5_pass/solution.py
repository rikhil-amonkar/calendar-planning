from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Copenhagen', 'Athens'),
        ('Copenhagen', 'Dubrovnik'),
        ('Munich', 'Tallinn'),
        ('Copenhagen', 'Munich'),
        ('Venice', 'Munich'),
        ('Reykjavik', 'Athens'),
        ('Athens', 'Dubrovnik'),
        ('Venice', 'Athens'),
        ('Lyon', 'Barcelona'),
        ('Copenhagen', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Athens', 'Munich'),
        ('Lyon', 'Munich'),
        ('Barcelona', 'Reykjavik'),
        ('Venice', 'Copenhagen'),
        ('Barcelona', 'Dubrovnik'),
        ('Lyon', 'Venice'),
        ('Dubrovnik', 'Munich'),
        ('Barcelona', 'Athens'),
        ('Copenhagen', 'Barcelona'),
        ('Venice', 'Barcelona'),
        ('Barcelona', 'Munich'),
        ('Barcelona', 'Tallinn'),
        ('Copenhagen', 'Tallinn')
    ]
    
    # Create flight connections dictionary
    flight_connections = {}
    for a, b in direct_flights:
        if a not in flight_connections:
            flight_connections[a] = []
        if b not in flight_connections:
            flight_connections[b] = []
        flight_connections[a].append(b)
        flight_connections[b].append(a)
    
    # Initialize Z3 solver
    s = Solver()
    
    # Days are 1..26
    days = 26
    day_city = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Create city mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: Each day must be assigned to a valid city
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: Total days per city must match requirements
    for city, days_needed in cities.items():
        city_id = city_ids[city]
        total = 0
        for day in day_city:
            total += If(day == city_id, 1, 0)
        s.add(total == days_needed)
    
    # Constraint: Barcelona between day 10-12
    barcelona_id = city_ids['Barcelona']
    s.add(Or([day_city[i] == barcelona_id for i in range(9, 12)]))
    
    # Constraint: Copenhagen between day 7-10
    copenhagen_id = city_ids['Copenhagen']
    s.add(Or([day_city[i] == copenhagen_id for i in range(6, 10)]))
    
    # Constraint: Dubrovnik between day 16-20
    dubrovnik_id = city_ids['Dubrovnik']
    s.add(Or([day_city[i] == dubrovnik_id for i in range(15, 20)]))
    
    # Constraint: Flight transitions must be direct
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        # Either stay in same city or take a direct flight
        same_city = current == next_day
        # Get all possible flight connections
        possible_flights = []
        current_city_name = id_to_city[current.as_long()] if is_const(current) else None
        next_city_name = id_to_city[next_day.as_long()] if is_const(next_day) else None
        
        if current_city_name and next_city_name:
            # If both are constants, check if they're connected
            if current_city_name != next_city_name:
                s.add((current_city_name, next_city_name) in direct_flights or 
                      (next_city_name, current_city_name) in direct_flights)
        else:
            # For symbolic variables, add general flight constraints
            for city_a, city_b in direct_flights:
                a_id = city_ids[city_a]
                b_id = city_ids[city_b]
                possible_flights.append(And(current == a_id, next_day == b_id))
                possible_flights.append(And(current == b_id, next_day == a_id))
            s.add(Or(same_city, *possible_flights))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_id = model.evaluate(day_city[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city, required in cities.items():
            assert city_days[city] == required, f"City {city} has {city_days[city]} days, expected {required}"
        
        # Check specific date constraints
        b_days = [entry['day'] for entry in itinerary if entry['place'] == 'Barcelona']
        assert any(10 <= day <= 12 for day in b_days), "Barcelona constraint failed"
        
        c_days = [entry['day'] for entry in itinerary if entry['place'] == 'Copenhagen']
        assert any(7 <= day <= 10 for day in c_days), "Copenhagen constraint failed"
        
        d_days = [entry['day'] for entry in itinerary if entry['place'] == 'Dubrovnik']
        assert any(16 <= day <= 20 for day in d_days), "Dubrovnik constraint failed"
        
        # Check flight connections
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert (current, next_place) in direct_flights or (next_place, current) in direct_flights, \
                    f"No direct flight between {current} and {next_place}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))