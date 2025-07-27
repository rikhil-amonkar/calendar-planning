from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Paris', 'Bucharest', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Create Z3 variables for each day (1..15)
    days = 15
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day variable must be between 0 and 3 (city indices)
    for day in day_vars:
        s.add(day >= 0, day <= 3)
    
    # Constraint: Days 1-7 must be Madrid (index 1)
    for i in range(7):
        s.add(day_vars[i] == city_to_idx['Madrid'])
    
    # Constraint: Days 14-15 must be Bucharest (index 2)
    s.add(day_vars[13] == city_to_idx['Bucharest'])
    s.add(day_vars[14] == city_to_idx['Bucharest'])
    
    # Constraints for city visits
    # Paris: 6 days
    paris_days = Sum([If(day == city_to_idx['Paris'], 1, 0) for day in day_vars])
    s.add(paris_days == 6)
    
    # Madrid: 7 days (already 7 days from 1-7)
    # So no additional constraints needed
    
    # Bucharest: 2 days (14-15)
    # So no additional constraints needed
    
    # Seville: 3 days
    seville_days = Sum([If(day == city_to_idx['Seville'], 1, 0) for day in day_vars])
    s.add(seville_days == 3)
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Either same city or connected by direct flight
        same_city = (current_city == next_city)
        flight_possible = Or([And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
                            for a in direct_flights 
                            for b in direct_flights[a]])
        s.add(Or(same_city, flight_possible))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        idx_to_city = {v: k for k, v in city_to_idx.items()}
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the counts
        counts = {'Paris': 0, 'Madrid': 0, 'Bucharest': 0, 'Seville': 0}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Ensure the counts meet the requirements
        assert counts['Paris'] == 6
        assert counts['Madrid'] == 7
        assert counts['Bucharest'] == 2
        assert counts['Seville'] == 3
        
        # Verify the flight constraints
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
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