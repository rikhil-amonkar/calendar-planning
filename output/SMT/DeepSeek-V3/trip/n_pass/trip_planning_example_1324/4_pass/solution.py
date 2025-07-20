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
    
    # Create a dictionary for faster lookup
    flight_dict = {}
    for a, b in direct_flights:
        if a not in flight_dict:
            flight_dict[a] = []
        if b not in flight_dict:
            flight_dict[b] = []
        flight_dict[a].append(b)
        flight_dict[b].append(a)
    
    # Initialize Z3 solver
    s = Solver()
    
    # Days are 1..26
    days = 26
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints that each day_city variable is within 0..8 (for 9 cities)
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: Total days per city must match the required days
    for city, required_days in cities.items():
        city_id = city_ids[city]
        total = 0
        for day in day_city:
            total += If(day == city_id, 1, 0)
        s.add(total == required_days)
    
    # Constraint: Barcelona must be visited between day 10 and 12 (inclusive)
    barcelona_id = city_ids['Barcelona']
    s.add(Or([day_city[i] == barcelona_id for i in range(9, 12)]))  # days 10-12 (0-based: 9,10,11)
    
    # Constraint: Copenhagen relatives visit between day 7 and 10
    copenhagen_id = city_ids['Copenhagen']
    s.add(Or([day_city[i] == copenhagen_id for i in range(6, 10)]))  # days 7-10 (0-based: 6,7,8,9)
    
    # Constraint: Dubrovnik wedding between day 16 and 20
    dubrovnik_id = city_ids['Dubrovnik']
    s.add(Or([day_city[i] == dubrovnik_id for i in range(15, 20)]))  # days 16-20 (0-based: 15..19)
    
    # Constraint: Flight transitions must be direct flights
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either same city or connected by flight
        same_city = current_city == next_city
        # Or connected by flight
        possible_flights = []
        for city_a, city_b in direct_flights:
            a_id = city_ids[city_a]
            b_id = city_ids[city_b]
            possible_flights.append(And(current_city == a_id, next_city == b_id))
            possible_flights.append(And(current_city == b_id, next_city == a_id))
        s.add(Or(same_city, *possible_flights))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_id = model.evaluate(day_city[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured this)
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city, required in cities.items():
            assert city_days[city] == required, f"City {city} has {city_days[city]} days, expected {required}"
        
        # Check Barcelona between day 10-12
        b_days = [entry['day'] for entry in itinerary if entry['place'] == 'Barcelona']
        assert any(10 <= day <= 12 for day in b_days), "Barcelona not visited between day 10-12"
        
        # Check Copenhagen between day 7-10
        c_days = [entry['day'] for entry in itinerary if entry['place'] == 'Copenhagen']
        assert any(7 <= day <= 10 for day in c_days), "Copenhagen not visited between day 7-10"
        
        # Check Dubrovnik between day 16-20
        d_days = [entry['day'] for entry in itinerary if entry['place'] == 'Dubrovnik']
        assert any(16 <= day <= 20 for day in d_days), "Dubrovnik not visited between day 16-20"
        
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