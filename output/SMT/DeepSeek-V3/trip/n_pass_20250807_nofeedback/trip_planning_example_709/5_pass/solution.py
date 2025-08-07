from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    # Direct flights adjacency list
    flights = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    total_days = 18
    day_vars = [Int(f'day_{i}') for i in range(total_days)]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day variable must be a valid city id
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Flight constraints: consecutive days must be connected by a direct flight or stay in same city
    for i in range(total_days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        constraints = []
        for city in cities:
            # Option to stay in same city
            same_city = And(current_day == city_ids[city], next_day == city_ids[city])
            constraints.append(same_city)
            # Options to fly to connected cities
            for neighbor in flights[city]:
                fly_to_neighbor = And(current_day == city_ids[city], next_day == city_ids[neighbor])
                constraints.append(fly_to_neighbor)
        s.add(Or(constraints))
    
    # Stay duration constraints
    for city in cities:
        required_days = cities[city]
        count = Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(total_days)])
        s.add(count == required_days)
    
    # Porto must be visited between days 16-18 (1-based)
    porto_in_last = Or([day_vars[i] == city_ids['Porto'] for i in [15, 16, 17]])
    s.add(porto_in_last)
    
    # Additional constraints to help guide the solver
    # Start in a city with many connections (Prague or Helsinki)
    s.add(Or(day_vars[0] == city_ids['Prague'], day_vars[0] == city_ids['Helsinki']))
    
    # Ensure we don't have too many consecutive flight days
    for i in range(total_days - 2):
        s.add(Not(And(
            day_vars[i] != day_vars[i+1],
            day_vars[i+1] != day_vars[i+2]
        )))
    
    # Ensure we visit all cities
    for city in cities:
        s.add(Or([day_vars[i] == city_ids[city] for i in range(total_days)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(total_days):
            city_id = m.evaluate(day_vars[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i + 1, 'place': city})
        
        # Verification
        stay_counts = {city: 0 for city in cities}
        for entry in itinerary:
            stay_counts[entry['place']] += 1
        for city in cities:
            assert stay_counts[city] == cities[city], f"Stay duration mismatch for {city}"
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i + 1]['place']
            if current != next_p:
                assert next_p in flights[current], f"Invalid flight from {current} to {next_p}"
        
        porto_visited = False
        for day in [16, 17, 18]:
            if itinerary[day - 1]['place'] == 'Porto':
                porto_visited = True
                break
        assert porto_visited, "Porto not visited in days 16-18"
        
        return {'itinerary': itinerary}
    else:
        return "No solution found"

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))