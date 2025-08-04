from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    Paris, Oslo, Porto, Geneva, Reykjavik = range(5)
    
    # Direct flights (bidirectional)
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
    bidirectional = set()
    for a, b in direct_flights:
        bidirectional.add((a, b))
        bidirectional.add((b, a))
    direct_flights = bidirectional
    
    # Total days
    total_days = 23
    
    # Create Z3 variables
    days = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(And(day >= 0, day <= 4))
    
    # Transition constraints
    for i in range(total_days - 1):
        current = days[i]
        next_c = days[i+1]
        # Either stay or take a direct flight
        s.add(Or(
            current == next_c,
            *[And(current == a, next_c == b) for (a, b) in direct_flights]
        ))
    
    # Fixed constraints
    # Geneva from day 1 to 7 (days 0-6)
    for i in range(7):
        s.add(days[i] == Geneva)
    
    # Oslo between day 19 and 23 (days 18-22)
    # At least one day must be Oslo in this range
    s.add(Or([days[i] == Oslo for i in range(18, 23)]))
    
    # Total days per city
    city_days = [
        (Paris, 6),
        (Oslo, 5),
        (Porto, 7),
        (Geneva, 7),
        (Reykjavik, 2)
    ]
    
    for city, required in city_days:
        total = Sum([If(d == city, 1, 0) for d in days])
        s.add(total == required)
    
    # Additional constraints to help the solver
    # Oslo must have exactly 5 days total
    # Geneva already has 7 fixed days
    
    # Check solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        
        # Verify all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
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
        
        # Verify flights
        for i in range(total_days - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                assert (city_map[current], city_map[next_p]) in direct_flights
        
        return {'itinerary': itinerary}
    else:
        return "No solution found"

solution = solve_itinerary()
print(solution)