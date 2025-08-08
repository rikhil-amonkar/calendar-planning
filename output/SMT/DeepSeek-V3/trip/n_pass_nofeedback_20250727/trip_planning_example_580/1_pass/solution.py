from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    Paris, Oslo, Porto, Geneva, Reykjavik = range(5)
    
    # Direct flights
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
    # Make it bidirectional
    bidirectional = set()
    for a, b in direct_flights:
        bidirectional.add((a, b))
        bidirectional.add((b, a))
    direct_flights = bidirectional
    
    # Total days
    total_days = 23
    
    # Create Z3 variables: day[i] is the city on day i+1 (since days are 1-based)
    days = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day must be one of the cities (0 to 4)
    for day in days:
        s.add(And(day >= 0, day <= 4))
    
    # Transition constraints: consecutive days must be the same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == a, next_city == b) for (a, b) in direct_flights]
        ))
    
    # Fixed constraints:
    # Geneva from day 1 to 7 (days 0..6 in 0-based)
    for i in range(7):
        s.add(days[i] == Geneva)
    
    # Oslo between day 19 and 23 (days 18..22 in 0-based)
    s.add(Or(*[days[i] == Oslo for i in range(18, 23)))
    
    # Total days per city
    city_days = [
        (Paris, 6),
        (Oslo, 5),
        (Porto, 7),
        (Geneva, 7),
        (Reykjavik, 2)
    ]
    
    for city, required_days in city_days:
        total = 0
        for day in days:
            total += If(day == city, 1, 0)
        s.add(total == required_days)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        
        # Verify transitions are valid
        for i in range(total_days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                a = city_map[current]
                b = city_map[next_place]
                assert (a, b) in direct_flights, f"Invalid flight from {current} to {next_place} on day {i+1}"
        
        # Verify day counts
        from collections import defaultdict
        counts = defaultdict(int)
        for entry in itinerary:
            counts[entry['place']] += 1
        assert counts['Paris'] == 6
        assert counts['Oslo'] == 5
        assert counts['Porto'] == 7
        assert counts['Geneva'] == 7
        assert counts['Reykjavik'] == 2
        
        # Verify fixed constraints
        for i in range(1, 8):
            assert itinerary[i-1]['place'] == 'Geneva', f"Day {i} not Geneva"
        oslo_days = [entry['day'] for entry in itinerary if entry['place'] == 'Oslo']
        assert any(19 <= day <= 23 for day in oslo_days), "Oslo not visited between day 19-23"
        
        return {'itinerary': itinerary}
    else:
        return "No solution found"

# Generate the solution
solution = solve_itinerary()
print(solution)