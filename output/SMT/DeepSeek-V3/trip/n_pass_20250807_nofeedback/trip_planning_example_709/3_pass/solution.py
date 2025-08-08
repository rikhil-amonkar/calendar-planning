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
    
    # Flight constraints: consecutive days must be connected by a direct flight or stay in the same city
    for i in range(total_days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        constraints = []
        for city in cities:
            # Option 1: stay in the same city
            same_city = And(current_day == city_ids[city], next_day == city_ids[city])
            constraints.append(same_city)
            # Option 2: fly to a neighboring city
            for neighbor in flights[city]:
                fly_to_neighbor = And(current_day == city_ids[city], next_day == city_ids[neighbor])
                constraints.append(fly_to_neighbor)
        s.add(Or(constraints))
    
    # Stay duration constraints
    for city in cities:
        required_days = cities[city]
        count = Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(total_days)])
        s.add(count == required_days)
    
    # Porto must be between day 16 and 18 (1-based, days 15-17 in 0-based)
    porto_days = []
    for i in [15, 16, 17]:  # 0-based days 15,16,17 (1-based 16,17,18)
        porto_days.append(day_vars[i] == city_ids['Porto'])
    s.add(Or(porto_days))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(total_days):
            city_id = m.evaluate(day_vars[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i + 1, 'place': city})
        
        # Verify the solution meets all constraints
        stay_counts = {city: 0 for city in cities}
        for entry in itinerary:
            stay_counts[entry['place']] += 1
        for city in cities:
            assert stay_counts[city] == cities[city], f"Stay duration for {city} does not match"
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert next_place in flights[current], f"No flight from {current} to {next_place}"
        
        porto_in_last = False
        for day in [16, 17, 18]:
            if itinerary[day - 1]['place'] == 'Porto':
                porto_in_last = True
                break
        assert porto_in_last, "Porto not visited in days 16-18"
        
        return {'itinerary': itinerary}
    else:
        return "No solution found"

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))