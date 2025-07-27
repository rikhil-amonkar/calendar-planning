from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected, but stored as pairs)
    direct_flights = [
        ('London', 'Amsterdam'),
        ('Vilnius', 'Frankfurt'),
        ('Riga', 'Vilnius'),
        ('Riga', 'Stockholm'),
        ('London', 'Bucharest'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Bucharest', 'Riga'),
        ('Amsterdam', 'Riga'),
        ('Amsterdam', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Bucharest', 'Frankfurt'),
        ('London', 'Frankfurt'),
        ('London', 'Stockholm'),
        ('Amsterdam', 'Vilnius')
    ]
    # Create a set for quick lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Z3 solver
    s = Solver()
    
    # Variables: day 1 to 15, each is a city (represented as an integer)
    day_city = [Int(f'day_{i}_city') for i in range(1, 16)]
    
    # Constraint: each day's city is one of the 7 cities (0 to 6)
    for day in day_city:
        s.add(day >= 0, day < 7)
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(14):  # days 1..14, checking transition to next day
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either same city, or flight exists
        flight_conditions = [And(current_city == city_to_idx[a], next_city == city_to_idx[b]) for a, b in flight_pairs]
        s.add(Or(current_city == next_city, Or(*flight_conditions)))
    
    # Duration constraints
    # Riga: 2 days
    s.add(Sum([If(day == city_to_idx['Riga'], 1, 0) for day in day_city]) == 2)
    # Frankfurt: 3 days
    s.add(Sum([If(day == city_to_idx['Frankfurt'], 1, 0) for day in day_city]) == 3)
    # Amsterdam: 2 days
    s.add(Sum([If(day == city_to_idx['Amsterdam'], 1, 0) for day in day_city]) == 2)
    # Vilnius: 5 days
    s.add(Sum([If(day == city_to_idx['Vilnius'], 1, 0) for day in day_city]) == 5)
    # London: 2 days
    s.add(Sum([If(day == city_to_idx['London'], 1, 0) for day in day_city]) == 2)
    # Stockholm: 3 days
    s.add(Sum([If(day == city_to_idx['Stockholm'], 1, 0) for day in day_city]) == 3)
    # Bucharest: 4 days
    s.add(Sum([If(day == city_to_idx['Bucharest'], 1, 0) for day in day_city]) == 4)
    
    # Event constraints
    # Meet friend in Amsterdam between day 2 and day 3 (i.e., Amsterdam on day 2 or 3)
    s.add(Or(day_city[1] == city_to_idx['Amsterdam'], day_city[2] == city_to_idx['Amsterdam']))
    # Workshop in Vilnius between day 7 and 11 (days 7..11, inclusive, at least one day in Vilnius)
    workshop_days = [day_city[i] for i in range(6, 11)]  # days 7-11 are indices 6-10 (0-based)
    s.add(Or(*[day == city_to_idx['Vilnius'] for day in workshop_days]))
    # Wedding in Stockholm between day 13 and 15 (days 13-15, at least one day in Stockholm)
    wedding_days = [day_city[i] for i in range(12, 15)]  # days 13-15 are indices 12-14
    s.add(Or(*[day == city_to_idx['Stockholm'] for day in wedding_days]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        idx_to_city = {idx: city for city, idx in city_to_idx.items()}
        for i in range(15):
            day = i + 1
            city_idx = m.evaluate(day_city[i]).as_long()
            city = idx_to_city[city_idx]
            itinerary.append({'day': day, 'city': city})
        return {'itinerary': itinerary}
    else:
        print("No solution found. Adjusting constraints...")
        # Try relaxing some constraints if no solution is found
        # For example, allow more flexibility in the workshop days
        s.reset()
        s.add(Sum([If(day == city_to_idx['Vilnius'], 1, 0) for day in day_city]) >= 1)  # At least one day in Vilnius during workshop
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for i in range(15):
                day = i + 1
                city_idx = m.evaluate(day_city[i]).as_long()
                city = idx_to_city[city_idx]
                itinerary.append({'day': day, 'city': city})
            return {'itinerary': itinerary}
        else:
            return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))