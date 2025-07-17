from z3 import *

def solve_itinerary():
    # Cities with correct spellings
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights - all bidirectional
    direct_flights = [
        ('Riga', 'Oslo'),
        ('Rome', 'Oslo'),
        ('Vienna', 'Milan'),
        ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'),
        ('Riga', 'Milan'),
        ('Lisbon', 'Oslo'),
        ('Rome', 'Riga'),
        ('Rome', 'Lisbon'),
        ('Vienna', 'Riga'),
        ('Vienna', 'Rome'),
        ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Vilnius'),
        ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'),
        ('Milan', 'Lisbon')
    ]
    
    # Create flight pairs in both directions
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    s = Solver()
    
    # Day variables (1-15)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    def city_day(city, day):
        return days[day - 1] == city_to_idx[city]
    
    # Total days constraints
    day_counts = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    for city, count in day_counts.items():
        s.add(Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(15)]) == count)
    
    # Fixed day constraints
    s.add(city_day('Vienna', 1))
    s.add(city_day('Vienna', 4))
    
    # Lisbon days 11-13
    for day in [11, 12, 13]:
        s.add(city_day('Lisbon', day))
    
    # Oslo days 13-15 (with day 13 already Lisbon)
    s.add(Or(city_day('Oslo', 14), city_day('Oslo', 15)))
    # Need one more Oslo day (total 3)
    
    # Flight transitions
    for i in range(14):
        current = days[i]
        next_day = days[i+1]
        same_city = current == next_day
        flight_possible = Or([And(current == city_to_idx[a], next_day == city_to_idx[b]) 
                           for a, b in flight_pairs])
        s.add(Or(same_city, flight_possible))
    
    # Additional constraints to help the solver
    # Ensure at least one transition happens
    s.add(Not(And([days[i] == days[i+1] for i in range(14)])))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            city_idx = model.evaluate(days[day - 1]).as_long()
            itinerary.append({'day': day, 'city': cities[city_idx]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['city']] += 1
        
        for city, count in day_counts.items():
            assert city_days[city] == count, f"Day count mismatch for {city}"
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))