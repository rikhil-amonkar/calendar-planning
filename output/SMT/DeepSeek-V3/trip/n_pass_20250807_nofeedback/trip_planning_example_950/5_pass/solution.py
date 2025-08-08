from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Mykonos': 3,
        'Riga': 3,
        'Munich': 4,
        'Bucharest': 4,
        'Rome': 4,
        'Nice': 3,
        'Krakow': 2
    }
    
    city_list = list(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    
    # Direct flights - make sure all are bidirectional
    flight_pairs = [
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
        ('Riga', 'Munich'),
        ('Rome', 'Riga')
    ]
    
    # Create both directions for each flight
    all_flights = set()
    for a, b in flight_pairs:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create Z3 solver and variables
    s = Solver()
    day_vars = [Int(f'day_{i}') for i in range(1, 18)]  # days 1 to 17
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(day >= 0, day < len(city_list))
    
    # Conference in Rome on days 1-4 (must be in Rome)
    for day in [0, 1, 2, 3]:  # days 1-4 (0-based)
        s.add(day_vars[day] == city_to_int['Rome'])
    
    # Wedding in Mykonos between day 4-6 (must be in Mykonos at least one of these days)
    # Also ensure total 3 days in Mykonos
    s.add(Or(
        day_vars[3] == city_to_int['Mykonos'],  # day4
        day_vars[4] == city_to_int['Mykonos'],  # day5
        day_vars[5] == city_to_int['Mykonos']   # day6
    ))
    
    # Annual show in Krakow on days 16-17 (must be in Krakow)
    s.add(day_vars[15] == city_to_int['Krakow'])
    s.add(day_vars[16] == city_to_int['Krakow'])
    
    # Flight constraints between consecutive days
    for i in range(len(day_vars) - 1):
        current = day_vars[i]
        next_day = day_vars[i+1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == city_to_int[a], next_day == city_to_int[b]) 
              for a, b in all_flights
            ]
        ))
    
    # Total days in each city must match requirements
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(len(day_vars))]) == days)
    
    # Additional constraint: Must visit Mykonos for exactly 3 days
    # (This is already covered by the total days constraint)
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 18):
            city_idx = m.evaluate(day_vars[day-1]).as_long()
            itinerary.append({'day': day, 'place': city_list[city_idx]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city, days in cities.items():
            assert city_days[city] == days, f"City {city} has {city_days[city]} days instead of {days}"
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert (current, next_place) in all_flights, f"No flight from {current} to {next_place}"
        
        assert itinerary[0]['place'] == 'Rome'
        assert itinerary[1]['place'] == 'Rome'
        assert itinerary[2]['place'] == 'Rome'
        assert itinerary[3]['place'] == 'Rome'
        assert any(itinerary[i]['place'] == 'Mykonos' for i in [3,4,5])
        assert itinerary[15]['place'] == 'Krakow'
        assert itinerary[16]['place'] == 'Krakow'
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
itinerary = solve_itinerary()
print(itinerary)