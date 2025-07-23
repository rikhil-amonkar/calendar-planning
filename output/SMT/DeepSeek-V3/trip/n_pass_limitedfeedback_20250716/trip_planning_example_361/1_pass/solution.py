from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Cities: Paris, Madrid, Bucharest, Seville
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    # Days are 1 to 15
    days = 15
    # Assign each day to a city (0: Paris, 1: Madrid, 2: Bucharest, 3: Seville)
    day_assignments = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Constraints for each day: must be 0, 1, 2, or 3
    for day in day_assignments:
        s.add(And(day >= 0, day <= 3))
    
    # Direct flights: possible transitions between cities
    direct_flights = {
        0: [1, 2, 3],  # Paris can fly to Madrid, Bucharest, Seville
        1: [0, 2, 3],  # Madrid can fly to Paris, Bucharest, Seville
        2: [0, 1],     # Bucharest can fly to Paris, Madrid
        3: [0, 1]      # Seville can fly to Paris, Madrid
    }
    
    # Constraint: transitions must be via direct flights
    for i in range(days - 1):
        current_day = day_assignments[i]
        next_day = day_assignments[i + 1]
        # Either stay in the same city or fly to a directly connected city
        s.add(Or(
            current_day == next_day,
            And([Or(next_day == dest for dest in direct_flights[current_day.as_long() if isinstance(current_day, int) else 0])])
        ))
    
    # Constraint: Days 1-7 must be Madrid (index 1)
    for i in range(7):
        s.add(day_assignments[i] == 1)
    
    # Constraint: Days 14 and 15 must be Bucharest (index 2)
    s.add(day_assignments[13] == 2)  # Day 14
    s.add(day_assignments[14] == 2)  # Day 15
    
    # Total days per city:
    # Paris: 6 days
    # Madrid: 7 days (already enforced for days 1-7, but flight days may add more)
    # Bucharest: 2 days (days 14-15)
    # Seville: 3 days
    
    # Function to count the days for a city
    def count_days(city_idx):
        return Sum([If(day == city_idx, 1, 0) for day in day_assignments])
    
    s.add(count_days(0) == 6)  # Paris
    s.add(count_days(1) == 7)  # Madrid
    s.add(count_days(2) == 2)  # Bucharest
    s.add(count_days(3) == 3)  # Seville
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(day_assignments[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Ensure the counts meet the constraints
        assert counts['Paris'] == 6
        assert counts['Madrid'] == 7
        assert counts['Bucharest'] == 2
        assert counts['Seville'] == 3
        
        # Verify transitions are via direct flights
        for i in range(days - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current_city != next_city:
                current_idx = city_to_int[current_city]
                next_idx = city_to_int[next_city]
                assert next_idx in direct_flights[current_idx]
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")