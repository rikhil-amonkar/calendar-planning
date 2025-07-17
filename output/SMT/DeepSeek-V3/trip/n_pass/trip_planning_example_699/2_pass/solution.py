from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Hamburg', 'Helsinki', 'London', 'Mykonos', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 16
    n_cities = len(cities)
    
    # Direct flights: adjacency list
    direct_flights = {
        'Dublin': ['London', 'Hamburg', 'Helsinki', 'Reykjavik'],
        'Hamburg': ['Dublin', 'London', 'Helsinki'],
        'Helsinki': ['Reykjavik', 'Dublin', 'Hamburg', 'London'],
        'London': ['Dublin', 'Hamburg', 'Reykjavik', 'Mykonos'],
        'Mykonos': ['London'],
        'Reykjavik': ['Helsinki', 'London', 'Dublin']
    }
    
    # Create Z3 variables: day[i] is the city index for day i+1 (since days start at 1)
    day = [Int(f'day_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Each day must be a valid city index (0 to n_cities-1)
    for d in day:
        s.add(And(d >= 0, d < n_cities))
    
    # Transition constraints: consecutive days must be the same city or have a direct flight
    for i in range(n_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # Either stay in the same city or move to a directly connected city
        transition_constraints = []
        for city_idx in range(n_cities):
            city = cities[city_idx]
            connected_cities = direct_flights.get(city, [])
            connected_indices = [city_map[c] for c in connected_cities if c in city_map]
            # Option 1: stay in the same city
            stay = (current_city == city_idx) & (next_city == city_idx)
            # Option 2: move to a connected city
            move = Or([And(current_city == city_idx, next_city == connected_idx) for connected_idx in connected_indices])
            transition_constraints.append(Or(stay, move))
        s.add(Or(transition_constraints))
    
    # City day constraints
    city_days = [
        ('Dublin', 5),
        ('Hamburg', 2),
        ('Helsinki', 4),
        ('London', 5),
        ('Mykonos', 3),
        ('Reykjavik', 2)
    ]
    
    for city, required_days in city_days:
        city_idx = city_map[city]
        s.add(Sum([If(day[i] == city_idx, 1, 0) for i in range(n_days)]) == required_days)
    
    # Specific constraints:
    # 1. Reykjavik wedding between day 9 and 10: so at least one of day 9 or 10 is Reykjavik
    reykjavik_idx = city_map['Reykjavik']
    s.add(Or(day[8] == reykjavik_idx, day[9] == reykjavik_idx))  # days are 0-based for 1-based days
    
    # 2. Dublin show from day 2 to 6: so days 1 to 5 (0-based) must include Dublin
    dublin_idx = city_map['Dublin']
    for i in range(1, 6):
        s.add(day[i] == dublin_idx)
    
    # 3. Hamburg friends between day 1 and 2: so day 0 or 1 is Hamburg
    hamburg_idx = city_map['Hamburg']
    s.add(Or(day[0] == hamburg_idx, day[1] == hamburg_idx))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        expected_counts = {
            'Dublin': 5,
            'Hamburg': 2,
            'Helsinki': 4,
            'London': 5,
            'Mykonos': 3,
            'Reykjavik': 2
        }
        assert city_counts == expected_counts, "City day counts do not match"
        
        # Check transitions
        for i in range(n_days - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                assert next_p in direct_flights[current], f"No direct flight from {current} to {next_p}"
        
        # Check specific day constraints
        # Reykjavik wedding between day 9 and 10
        assert (itinerary[8]['place'] == 'Reykjavik') or (itinerary[9]['place'] == 'Reykjavik'), "Reykjavik wedding constraint not met"
        
        # Dublin show days 2-6 (1-5 0-based)
        for i in range(1, 6):
            assert itinerary[i]['place'] == 'Dublin', "Dublin show days not met"
        
        # Hamburg friends day 1-2 (0-1 0-based)
        assert (itinerary[0]['place'] == 'Hamburg') or (itinerary[1]['place'] == 'Hamburg'), "Hamburg friends constraint not met"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")