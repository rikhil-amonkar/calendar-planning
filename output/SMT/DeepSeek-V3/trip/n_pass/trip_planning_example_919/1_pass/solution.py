from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: each pair is bidirectional
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
    
    # Create a set of direct flight pairs for easy lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Z3 solver
    s = Solver()
    
    # Variables: day_1 to day_15, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 16)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Helper functions
    def city_day(city, day):
        return days[day - 1] == city_to_idx[city]
    
    # Constraints
    # 1. Total days in each city:
    # Vienna: 4 days (including days 1 and 4)
    # Milan: 2 days
    # Rome: 3 days
    # Riga: 2 days
    # Lisbon: 3 days (days 11-13 must be in Lisbon)
    # Vilnius: 4 days
    # Oslo: 3 days (days 13-15 must include Oslo)
    
    # Count days per city
    for city, required_days in [
        ('Vienna', 4),
        ('Milan', 2),
        ('Rome', 3),
        ('Riga', 2),
        ('Lisbon', 3),
        ('Vilnius', 4),
        ('Oslo', 3)
    ]:
        count = 0
        for day in range(1, 16):
            count += If(days[day - 1] == city_to_idx[city], 1, 0)
        s.add(count == required_days)
    
    # 2. Specific day constraints:
    # Day 1 and Day 4 in Vienna
    s.add(days[0] == city_to_idx['Vienna'])
    s.add(days[3] == city_to_idx['Vienna'])
    
    # Lisbon between day 11-13: days 11,12,13 are in Lisbon
    for day in [11, 12, 13]:
        s.add(days[day - 1] == city_to_idx['Lisbon'])
    
    # Oslo between day 13-15: at least days 14 and 15, since day 13 is Lisbon. But total Oslo days is 3.
    s.add(Or(days[13] == city_to_idx['Oslo'], days[14] == city_to_idx['Oslo']))
    # We need two more Oslo days elsewhere.
    
    # 3. Flight constraints: consecutive days must be same city or have a direct flight.
    for day in range(1, 15):
        current_city = days[day - 1]
        next_city = days[day]
        # Either same city or there's a direct flight
        same_city = current_city == next_city
        flight_exists = Or([And(current_city == city_to_idx[a], next_city == city_to_idx[b]) for a, b in flight_pairs])
        s.add(Or(same_city, flight_exists))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            city_idx = model.evaluate(days[day - 1]).as_long()
            itinerary.append({'day': day, 'city': cities[city_idx]})
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))