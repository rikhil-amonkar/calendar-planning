from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights between cities
    direct_flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Valencia', 'Vilnius', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Stuttgart': ['Valencia', 'Istanbul', 'Reykjavik'],
        'Munich': ['Reykjavik', 'Geneva', 'Vilnius', 'Seville', 'Istanbul'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Vilnius': ['Istanbul', 'Munich']
    }
    
    # Create mapping from city index to possible next city indices
    next_cities = {}
    for city in cities:
        next_cities[city_index[city]] = [city_index[c] for c in direct_flights[city]]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create day variables (1-25)
    days = [Int(f'day_{i}') for i in range(1, 26)]
    
    # Each day must be a valid city index
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints
    # Reykjavik: days 1-3
    s.add(days[0] == city_index['Reykjavik'])
    s.add(days[1] == city_index['Reykjavik'])
    s.add(days[2] == city_index['Reykjavik'])
    
    # Stuttgart: days 4 and 7
    s.add(days[3] == city_index['Stuttgart'])
    s.add(days[6] == city_index['Stuttgart'])
    
    # Munich: days 13-15
    s.add(days[12] == city_index['Munich'])
    s.add(days[13] == city_index['Munich'])
    s.add(days[14] == city_index['Munich'])
    
    # Istanbul: days 19-22
    s.add(days[18] == city_index['Istanbul'])
    s.add(days[19] == city_index['Istanbul'])
    s.add(days[20] == city_index['Istanbul'])
    s.add(days[21] == city_index['Istanbul'])
    
    # Duration constraints
    s.add(Sum([If(days[i] == city_index['Stuttgart'], 1, 0) for i in range(25)]) == 4)
    s.add(Sum([If(days[i] == city_index['Istanbul'], 1, 0) for i in range(25)]) == 4)
    s.add(Sum([If(days[i] == city_index['Vilnius'], 1, 0) for i in range(25)]) == 4)
    s.add(Sum([If(days[i] == city_index['Seville'], 1, 0) for i in range(25)]) == 3)
    s.add(Sum([If(days[i] == city_index['Geneva'], 1, 0) for i in range(25)]) == 5)
    s.add(Sum([If(days[i] == city_index['Valencia'], 1, 0) for i in range(25)]) == 5)
    s.add(Sum([If(days[i] == city_index['Munich'], 1, 0) for i in range(25)]) == 3)
    s.add(Sum([If(days[i] == city_index['Reykjavik'], 1, 0) for i in range(25)]) == 4)
    
    # Flight constraints
    for i in range(24):
        current = days[i]
        next_day = days[i+1]
        # Create constraints for each possible current city
        constraints = []
        for city_idx in next_cities:
            constraints.append(And(current == city_idx, Or([next_day == idx for idx in next_cities[city_idx]])))
        s.add(Or(next_day == current, Or(constraints)))
    
    # Solve and return itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 26):
            day_var = days[i-1]
            city_idx = model[day_var].as_long()
            itinerary.append({'day': i, 'city': cities[city_idx]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['city']] += 1
        
        expected_counts = {
            'Stuttgart': 4,
            'Istanbul': 4,
            'Vilnius': 4,
            'Seville': 3,
            'Geneva': 5,
            'Valencia': 5,
            'Munich': 3,
            'Reykjavik': 4
        }
        
        for city in counts:
            if counts[city] != expected_counts[city]:
                print(f"Warning: {city} has {counts[city]} days (expected {expected_counts[city]})")
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))