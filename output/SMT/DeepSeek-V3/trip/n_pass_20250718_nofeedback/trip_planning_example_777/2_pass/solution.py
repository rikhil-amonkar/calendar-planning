from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    adjacency = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Reykjavik', 'Dublin'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Riga', 'Dublin', 'Helsinki'],
        'Dublin': ['Riga', 'Helsinki', 'Tallinn', 'Vienna', 'Reykjavik']
    }
    
    # Create Z3 variables: day 1 to 15, each is a city index (0 to 5)
    day_city = [Int(f'day_{i}_city') for i in range(1, 16)]
    
    s = Solver()
    
    # Each day's city must be between 0 and 5
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # City day counts
    required_days = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    # Ensure the total days per city match requirements
    for city, idx in city_indices.items():
        s.add(Sum([If(day == idx, 1, 0) for day in day_city]) == required_days[city])
    
    # Flight constraints: consecutive days must be same city or adjacent
    for i in range(len(day_city) - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either stay in the same city or move to an adjacent city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_indices[a], next_city == city_indices[b]) 
              for a in adjacency for b in adjacency[a] if a in city_indices and b in city_indices]
        ))
    
    # Specific constraints:
    # Vienna: show from day 2 to day 3 (so day 2 and 3 must be Vienna)
    s.add(day_city[1] == city_indices['Vienna'])  # day 2 is index 1
    s.add(day_city[2] == city_indices['Vienna'])  # day 3 is index 2
    
    # Helsinki friends between day 3 and day 5 (so day 3,4,5: but day3 is Vienna, so Helsinki must be day4 or day5)
    s.add(Or(
        day_city[3] == city_indices['Helsinki'],  # day4
        day_city[4] == city_indices['Helsinki']   # day5
    ))
    
    # Tallinn wedding between day7 and day11 (days 7-11 are indices 6-10)
    # At least one day in Tallinn between these days
    s.add(Or([day_city[i] == city_indices['Tallinn'] for i in range(6, 11)]))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 16):
            city_idx = model.evaluate(day_city[i-1]).as_long()
            itinerary.append({'day': i, 'place': cities[city_idx]})
        
        # Verify day counts per city
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        for city in cities:
            assert counts[city] == required_days[city], f"City {city} has {counts[city]} days instead of {required_days[city]}"
        
        # Verify flight constraints
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert next_place in adjacency[current], f"No direct flight from {current} to {next_place} on day {i+1}"
        
        # Verify specific constraints
        assert itinerary[1]['place'] == 'Vienna' and itinerary[2]['place'] == 'Vienna', "Vienna show not on days 2-3"
        assert any(itinerary[i]['place'] == 'Helsinki' for i in [3,4]), "Helsinki friends not met between days 3-5"
        assert any(itinerary[i]['place'] == 'Tallinn' for i in range(6,11)), "Tallinn wedding not attended between days 7-11"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")