from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Rome', 'Nice', 'Riga', 'Bucharest', 'Munich', 'Mykonos', 'Krakow']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: each pair is bidirectional except Riga to Munich is one way
    direct_flights = [
        ('Nice', 'Riga'),
        ('Bucharest', 'Munich'),
        ('Mykonos', 'Munich'),
        ('Riga', 'Bucharest'),
        ('Rome', 'Nice'),
        ('Rome', 'Munich'),
        ('Mykonos', 'Nice'),
        ('Rome', 'Mykonos'),
        ('Munich', 'Krakow'),
        ('Rome', 'Bucharest'),
        ('Nice', 'Munich'),
        ('Riga', 'Munich'),  # Riga to Munich is one way
        ('Rome', 'Riga')
    ]
    
    # Create an adjacency list for flights
    adjacency = {city: set() for city in cities}
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)  # assuming most are bidirectional
    
    # Adjust for one-way flight from Riga to Munich
    if 'Riga' in adjacency['Munich']:
        adjacency['Munich'].remove('Riga')
    
    # Z3 variables: assign each day to a city (0..6)
    s = Solver()
    days = 17
    day_assignments = [Int(f'day_{i}') for i in range(days)]
    for day in day_assignments:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for each city's total days
    city_days = [
        ('Rome', 4),
        ('Nice', 3),
        ('Riga', 3),
        ('Bucharest', 4),
        ('Munich', 4),
        ('Mykonos', 3),
        ('Krakow', 2)
    ]
    
    # Fixed constraints:
    # Rome must be days 1-4 (0-based: 0-3)
    for i in range(4):
        s.add(day_assignments[i] == city_indices['Rome'])
    
    # Krakow must be days 16-17 (0-based: 15-16)
    s.add(day_assignments[15] == city_indices['Krakow'])
    s.add(day_assignments[16] == city_indices['Krakow'])
    
    # Mykonos wedding between day 4 and 6 (1-based: days 4-6 are 3-5 in 0-based)
    # At least one of days 3,4,5 must be Mykonos
    s.add(Or(day_assignments[3] == city_indices['Mykonos'],
             day_assignments[4] == city_indices['Mykonos'],
             day_assignments[5] == city_indices['Mykonos']))
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(days - 1):
        current_city = day_assignments[i]
        next_city = day_assignments[i + 1]
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_indices[a], next_city == city_indices[b]) 
                            for a in adjacency for b in adjacency[a]])
        s.add(Or(same_city, flight_possible))
    
    # Total days per city
    for city, total in city_days:
        city_idx = city_indices[city]
        s.add(Sum([If(day_assignments[i] == city_idx, 1, 0) for i in range(days)]) == total)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_idx = m.evaluate(day_assignments[i]).as_long()
            itinerary.append({'day': i + 1, 'place': cities[city_idx]})
        
        # Verify the solution meets all constraints
        mykonos_days = [d['day'] for d in itinerary if d['place'] == 'Mykonos']
        assert len(mykonos_days) == 3
        assert any(4 <= day <= 6 for day in mykonos_days)
        
        rome_days = [d['day'] for d in itinerary if d['place'] == 'Rome']
        assert all(1 <= day <= 4 for day in rome_days)
        assert len(rome_days) == 4
        
        krakow_days = [d['day'] for d in itinerary if d['place'] == 'Krakow']
        assert krakow_days == [16, 17]
        
        for i in range(days - 1):
            current_place = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current_place != next_place:
                assert next_place in adjacency[current_place]
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
print(json.dumps(result, indent=2))