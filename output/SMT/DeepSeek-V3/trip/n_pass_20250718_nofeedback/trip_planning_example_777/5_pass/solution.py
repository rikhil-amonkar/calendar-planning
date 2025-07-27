from z3 import *
import json

def solve_itinerary():
    # Cities with indices
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flights = [
        ('Helsinki', 'Riga'),
        ('Helsinki', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Helsinki', 'Reykjavik'),
        ('Riga', 'Tallinn'),
        ('Riga', 'Vienna'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Reykjavik'),
        ('Vienna', 'Dublin'),
        ('Reykjavik', 'Dublin'),
        ('Tallinn', 'Dublin')
    ]
    
    # Create flight adjacency dictionary
    adjacency = {city: set() for city in cities}
    for a, b in flights:
        adjacency[a].add(b)
        adjacency[b].add(a)
    
    # Create solver
    s = Solver()
    
    # Day variables (day 1 to 15)
    day_city = [Int(f'day_{i}') for i in range(1, 16)]
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Required days in each city
    required_days = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    # Count days in each city
    for city, idx in city_idx.items():
        count = Sum([If(day == idx, 1, 0) for day in day_city])
        s.add(count == required_days[city])
    
    # Flight constraints between consecutive days
    for i in range(14):
        current = day_city[i]
        next_day = day_city[i+1]
        # Either stay or fly to adjacent city
        s.add(Or(
            current == next_day,
            *[And(current == city_idx[a], next_day == city_idx[b]) 
              for a in adjacency for b in adjacency[a]]
        ))
    
    # Specific constraints:
    # Vienna show on days 2-3 (must be in Vienna both days)
    s.add(day_city[1] == city_idx['Vienna'])  # day 2
    s.add(day_city[2] == city_idx['Vienna'])  # day 3
    
    # Helsinki friends between days 3-5 (must be in Helsinki on at least one day in this range)
    s.add(Or(
        day_city[2] == city_idx['Helsinki'],  # day 3
        day_city[3] == city_idx['Helsinki'],   # day 4
        day_city[4] == city_idx['Helsinki']    # day 5
    ))
    
    # Tallinn wedding between days 7-11 (must be in Tallinn on at least one day in this range)
    s.add(Or([day_city[i] == city_idx['Tallinn'] for i in range(6, 11)]))
    
    # Try to find solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 16):
            city_idx_val = model.evaluate(day_city[i-1]).as_long()
            itinerary.append({'day': i, 'place': cities[city_idx_val]})
        
        # Verify all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify day counts
        for city in cities:
            assert counts[city] == required_days[city], f"City {city} has wrong day count"
        
        # Verify flight connections
        for i in range(14):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                assert next_p in adjacency[current], f"Invalid flight from {current} to {next_p}"
        
        # Verify specific events
        assert itinerary[1]['place'] == 'Vienna' and itinerary[2]['place'] == 'Vienna'
        assert any(itinerary[i]['place'] == 'Helsinki' for i in range(2,5))
        assert any(itinerary[i]['place'] == 'Tallinn' for i in range(6,11))
        
        return {'itinerary': itinerary}
    else:
        print("Failed to find solution. Constraints may be too restrictive.")
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found")