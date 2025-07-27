from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights
    direct_flights = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Paris', 'Bucharest', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Create solver and day variables
    s = Solver()
    day_vars = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Each day must be assigned to a city
    for day in day_vars:
        s.add(day >= 0, day <= 3)
    
    # Fixed days: Madrid (1-7), Bucharest (14-15)
    for i in range(7):
        s.add(day_vars[i] == city_to_idx['Madrid'])
    s.add(day_vars[13] == city_to_idx['Bucharest'])
    s.add(day_vars[14] == city_to_idx['Bucharest'])
    
    # Count days in each city
    paris_days = Sum([If(day == city_to_idx['Paris'], 1, 0) for day in day_vars])
    seville_days = Sum([If(day == city_to_idx['Seville'], 1, 0) for day in day_vars])
    
    s.add(paris_days == 6)
    s.add(seville_days == 3)
    
    # Flight constraints
    for i in range(14):  # Only need to check up to day 14
        current = day_vars[i]
        next_day = day_vars[i+1]
        same_city = (current == next_day)
        flight_possible = Or([And(current == city_to_idx[a], next_day == city_to_idx[b])
                            for a in direct_flights for b in direct_flights[a]])
        s.add(Or(same_city, flight_possible))
    
    # Additional constraints to help the solver
    # Days 8-13 must be either Paris or Seville (since Madrid is already covered)
    for i in range(7, 13):
        s.add(Or(day_vars[i] == city_to_idx['Paris'], 
                day_vars[i] == city_to_idx['Seville']))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        idx_to_city = {v: k for k, v in city_to_idx.items()}
        
        for i in range(15):
            day_num = i + 1
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Paris'] == 6
        assert counts['Madrid'] == 7
        assert counts['Bucharest'] == 2
        assert counts['Seville'] == 3
        
        # Verify flights
        for i in range(14):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert next_place in direct_flights[current]
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")