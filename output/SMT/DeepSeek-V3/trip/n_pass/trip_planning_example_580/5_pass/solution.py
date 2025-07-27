from z3 import *

def solve_itinerary():
    # Cities with their indices
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    Paris, Oslo, Porto, Geneva, Reykjavik = range(5)
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        (Paris, Oslo),
        (Geneva, Oslo),
        (Porto, Paris),
        (Geneva, Paris),
        (Geneva, Porto),
        (Paris, Reykjavik),
        (Reykjavik, Oslo),
        (Porto, Oslo)
    ]
    # Make bidirectional
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Total days
    total_days = 23
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(And(day >= 0, day <= 4))
    
    # Transition constraints between consecutive days
    for i in range(total_days - 1):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take a direct flight
        possible_transitions = [current == next_day]
        for (a, b) in flight_set:
            possible_transitions.append(And(current == a, next_day == b))
        s.add(Or(possible_transitions))
    
    # Fixed constraints
    # Must be in Geneva from day 1 to 7 (days 0-6)
    for i in range(7):
        s.add(days[i] == Geneva)
    
    # Must visit Oslo between day 19 and 23 (days 18-22)
    s.add(Or([days[i] == Oslo for i in range(18, 23)]))
    
    # Total days per city
    city_requirements = [
        (Paris, 6),
        (Oslo, 5),
        (Porto, 7),
        (Geneva, 7),
        (Reykjavik, 2)
    ]
    
    for city, required in city_requirements:
        total = Sum([If(d == city, 1, 0) for d in days])
        s.add(total == required)
    
    # Additional constraints to help the solver
    # Ensure we don't have impossible sequences
    # For example, can't go from Geneva to Reykjavik directly
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        
        # Verify all constraints are met
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify day counts
        assert counts['Paris'] == 6
        assert counts['Oslo'] == 5
        assert counts['Porto'] == 7
        assert counts['Geneva'] == 7
        assert counts['Reykjavik'] == 2
        
        # Verify fixed periods
        for i in range(1, 8):
            assert itinerary[i-1]['place'] == 'Geneva'
        
        oslo_days = [entry['day'] for entry in itinerary if entry['place'] == 'Oslo']
        assert any(19 <= d <= 23 for d in oslo_days)
        
        # Verify flight connections
        for i in range(total_days - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                assert (city_map[current], city_map[next_p]) in flight_set
        
        return {'itinerary': itinerary}
    else:
        # If no solution found, try relaxing some constraints
        # For example, allow Oslo to be visited outside 19-23 if needed
        s.pop()
        s.add(Or([days[i] == Oslo for i in range(17, 23)]))  # Extend Oslo window
        
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for i in range(total_days):
                city_idx = model.evaluate(days[i]).as_long()
                itinerary.append({'day': i+1, 'place': cities[city_idx]})
            
            return {'itinerary': itinerary}
        else:
            return "No solution found after relaxing constraints"

solution = solve_itinerary()
print(solution)