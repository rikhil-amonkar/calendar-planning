from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Reykjavik': 5,
        'Istanbul': 4,
        'Edinburgh': 5,
        'Oslo': 2,
        'Stuttgart': 3,
        'Bucharest': 5
    }
    city_list = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_list)}
    n_days = 19
    
    # Direct flights (undirected)
    direct_flights = [
        ('Bucharest', 'Oslo'),
        ('Istanbul', 'Oslo'),
        ('Reykjavik', 'Stuttgart'),
        ('Bucharest', 'Istanbul'),
        ('Stuttgart', 'Edinburgh'),
        ('Istanbul', 'Edinburgh'),
        ('Oslo', 'Reykjavik'),
        ('Istanbul', 'Stuttgart'),
        ('Oslo', 'Edinburgh')
    ]
    
    # Create neighbor sets for each city
    neighbors = {city: set() for city in city_list}
    for a, b in direct_flights:
        neighbors[a].add(b)
        neighbors[b].add(a)
    
    # Initialize Z3 solver
    s = Solver()
    
    # day_place[i] represents city on day i+1 (1-based)
    day_place = [Int(f'day_{i+1}') for i in range(n_days)]
    
    # Each day must be a valid city index
    for day in day_place:
        s.add(day >= 0, day < len(city_list))
    
    # Transition constraints: must stay or fly to connected city
    for i in range(n_days - 1):
        current = day_place[i]
        next_city = day_place[i+1]
        s.add(Or(
            current == next_city,  # Stay in same city
            Or([And(current == city_to_idx[a], next_city == city_to_idx[b])
                for a in city_list for b in neighbors[a]])
        ))
    
    # Total days per city
    for city in city_list:
        s.add(Sum([If(day_place[i] == city_to_idx[city], 1, 0) 
               for i in range(n_days)]) == cities[city]
    
    # Istanbul must include days 5-8 (1-based)
    istanbul_idx = city_to_idx['Istanbul']
    s.add(Or([day_place[i] == istanbul_idx for i in range(4, 8)]))
    
    # Oslo must include days 8-9 (1-based)
    oslo_idx = city_to_idx['Oslo']
    s.add(Or(day_place[7] == oslo_idx, day_place[8] == oslo_idx))
    
    # Additional constraints to help solver
    # Must start somewhere (arbitrary choice)
    s.add(day_place[0] == city_to_idx['Reykjavik'])
    
    # Must end somewhere (arbitrary choice)
    s.add(day_place[-1] == city_to_idx['Bucharest'])
    
    # Try to find solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = m.evaluate(day_place[i]).as_long()
            itinerary.append({"day": i+1, "place": city_list[city_idx]})
        
        # Verify solution
        counts = {city: 0 for city in city_list}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Check day counts
        for city in cities:
            assert counts[city] == cities[city], f"Day count mismatch for {city}"
        
        # Check transitions
        for i in range(n_days - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                assert next_p in neighbors[current], f"Invalid flight {current}->{next_p}"
        
        # Check timing constraints
        ist_days = [e['day'] for e in itinerary if e['place'] == 'Istanbul']
        assert any(5 <= d <= 8 for d in ist_days), "Istanbul timing failed"
        
        oslo_days = [e['day'] for e in itinerary if e['place'] == 'Oslo']
        assert any(8 <= d <= 9 for d in oslo_days), "Oslo timing failed"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))