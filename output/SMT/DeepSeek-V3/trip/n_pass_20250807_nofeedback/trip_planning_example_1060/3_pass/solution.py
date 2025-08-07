from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as adjacency list
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
    
    # Create a mapping from city to its possible next cities (indices)
    next_cities = {}
    for city in cities:
        next_cities[city_index[city]] = [city_index[c] for c in direct_flights[city]]
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: day_1 to day_25, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 26)]
    
    # Each day variable must be between 0 and 7 (representing the index in cities list)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints
    # Reykjavik: days 1-3
    s.add(days[0] == city_index['Reykjavik'])
    s.add(days[1] == city_index['Reykjavik'])
    s.add(days[2] == city_index['Reykjavik'])
    
    # Stuttgart: conference on day 4 and day 7 (1-based)
    s.add(days[3] == city_index['Stuttgart'])  # day 4
    s.add(days[6] == city_index['Stuttgart'])  # day 7
    
    # Munich annual show from day 13 to 15 (days 13,14,15)
    s.add(days[12] == city_index['Munich'])
    s.add(days[13] == city_index['Munich'])
    s.add(days[14] == city_index['Munich'])
    
    # Istanbul relatives between day 19 and 22 (days 19,20,21,22)
    s.add(days[18] == city_index['Istanbul'])
    s.add(days[19] == city_index['Istanbul'])
    s.add(days[20] == city_index['Istanbul'])
    s.add(days[21] == city_index['Istanbul'])
    
    # Duration constraints
    # Stuttgart: total 4 days (including days 4 and 7)
    s.add(Sum([If(days[i] == city_index['Stuttgart'], 1, 0) for i in range(25)]) == 4)
    
    # Istanbul: total 4 days (including days 19-22)
    s.add(Sum([If(days[i] == city_index['Istanbul'], 1, 0) for i in range(25)]) == 4)
    
    # Vilnius: 4 days
    s.add(Sum([If(days[i] == city_index['Vilnius'], 1, 0) for i in range(25)]) == 4)
    
    # Seville: 3 days
    s.add(Sum([If(days[i] == city_index['Seville'], 1, 0) for i in range(25)]) == 3)
    
    # Geneva: 5 days
    s.add(Sum([If(days[i] == city_index['Geneva'], 1, 0) for i in range(25)]) == 5)
    
    # Valencia: 5 days
    s.add(Sum([If(days[i] == city_index['Valencia'], 1, 0) for i in range(25)]) == 5)
    
    # Munich: 3 days (including days 13-15)
    s.add(Sum([If(days[i] == city_index['Munich'], 1, 0) for i in range(25)]) == 3)
    
    # Reykjavik: 4 days (including days 1-3)
    s.add(Sum([If(days[i] == city_index['Reykjavik'], 1, 0) for i in range(25)]) == 4)
    
    # Flight constraints: consecutive days must be connected by direct flights or same city
    for i in range(24):
        current_city = days[i]
        next_city = days[i+1]
        # For each possible current city, next city must be in its next_cities or same city
        s.add(Or(
            next_city == current_city,
            *[next_city == idx for idx in next_cities[current_city.as_long() if is_expr(current_city) else current_city]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 26):
            day_var = days[i-1]
            city_idx = model[day_var].as_long()
            itinerary.append({'day': i, 'city': cities[city_idx]})
        
        # Verify the solution meets all constraints (sanity check)
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
                print(f"City {city} has {counts[city]} days, expected {expected_counts[city]}")
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute the solver
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))