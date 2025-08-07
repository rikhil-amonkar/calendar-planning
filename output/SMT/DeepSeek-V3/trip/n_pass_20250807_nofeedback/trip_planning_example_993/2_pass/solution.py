from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
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
    
    # Create a set of tuples representing direct flights
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((city_map[a], city_map[b]))
        flight_set.add((city_map[b], city_map[a]))
    
    # Z3 variables: day[i] is the city visited on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]  # days 1 to 15
    
    s = Solver()
    
    # Each day's assignment must be a valid city index (0 to 6)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for each city's total days
    # Riga: 2 days
    s.add(Sum([If(day == city_map['Riga'], 1, 0) for day in days]) == 2)
    # Frankfurt: 3 days
    s.add(Sum([If(day == city_map['Frankfurt'], 1, 0) for day in days]) == 3)
    # Amsterdam: 2 days
    s.add(Sum([If(day == city_map['Amsterdam'], 1, 0) for day in days]) == 2)
    # Vilnius: 5 days
    s.add(Sum([If(day == city_map['Vilnius'], 1, 0) for day in days]) == 5)
    # London: 2 days
    s.add(Sum([If(day == city_map['London'], 1, 0) for day in days]) == 2)
    # Stockholm: 3 days
    s.add(Sum([If(day == city_map['Stockholm'], 1, 0) for day in days]) == 3)
    # Bucharest: 4 days
    s.add(Sum([If(day == city_map['Bucharest'], 1, 0) for day in days]) == 4)
    
    # Special constraints:
    # Meet friend in Amsterdam between day 2 and day 3 (i.e., Amsterdam must be on day 2 or 3)
    s.add(Or(days[1] == city_map['Amsterdam'], days[2] == city_map['Amsterdam']))
    
    # Workshop in Vilnius between day 7 and 11 (i.e., at least one day between 7-11 must be Vilnius)
    s.add(Or([days[i] == city_map['Vilnius'] for i in range(6, 11)]))  # days 7-11 are indices 6-10 (0-based)
    
    # Wedding in Stockholm between day 13 and 15 (i.e., at least one day between 13-15 must be Stockholm)
    s.add(Or([days[i] == city_map['Stockholm'] for i in range(12, 15)]))  # days 13-15 are indices 12-14
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(14):  # from day 1 to day 15 (indices 0 to 14)
        current = days[i]
        next_day = days[i+1]
        # Either stay in the same city or have a direct flight
        s.add(Or(current == next_day, 
                 Or([And(current == a, next_day == b) for (a, b) in flight_set])))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 16):
            city_idx = model.evaluate(days[i-1]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': i, 'place': city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should ensure it's correct)
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))