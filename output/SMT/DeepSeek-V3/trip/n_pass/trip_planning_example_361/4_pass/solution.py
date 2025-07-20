from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Cities and their indices
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Days are 1 to 15
    days = 15
    # Assign each day to a city (0: Paris, 1: Madrid, 2: Bucharest, 3: Seville)
    day_assignments = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Constraints for each day: must be 0, 1, 2, or 3
    for day in day_assignments:
        s.add(And(day >= 0, day <= 3))
    
    # Direct flights between cities
    direct_flights = {
        0: [1, 2, 3],  # Paris can fly to Madrid, Bucharest, Seville
        1: [0, 2, 3],  # Madrid can fly to Paris, Bucharest, Seville
        2: [0, 1],     # Bucharest can fly to Paris, Madrid
        3: [0, 1]      # Seville can fly to Paris, Madrid
    }
    
    # Constraint: transitions must be via direct flights
    for i in range(days - 1):
        current = day_assignments[i]
        next_day = day_assignments[i + 1]
        # Either stay in same city or fly to connected city
        s.add(Or(
            current == next_day,
            *[next_day == dest for dest in direct_flights[current.as_long() if isinstance(current, int) else 0]]
        ))
    
    # Constraint: Days 1-7 must be Madrid (index 1)
    for i in range(7):
        s.add(day_assignments[i] == city_idx['Madrid'])
    
    # Constraint: Days 14 and 15 must be Bucharest (index 2)
    s.add(day_assignments[13] == city_idx['Bucharest'])  # Day 14
    s.add(day_assignments[14] == city_idx['Bucharest'])  # Day 15
    
    # Total days per city
    def count_days(city):
        return Sum([If(day == city_idx[city], 1, 0) for day in day_assignments])
    
    s.add(count_days('Paris') == 6)
    s.add(count_days('Madrid') == 7)
    s.add(count_days('Seville') == 3)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_idx_val = model.evaluate(day_assignments[i]).as_long()
            city = cities[city_idx_val]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Ensure counts meet constraints
        assert counts['Paris'] == 6
        assert counts['Madrid'] == 7
        assert counts['Bucharest'] == 2
        assert counts['Seville'] == 3
        
        # Verify transitions are via direct flights
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current != next_city:
                assert city_idx[next_city] in direct_flights[city_idx[current]]
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")