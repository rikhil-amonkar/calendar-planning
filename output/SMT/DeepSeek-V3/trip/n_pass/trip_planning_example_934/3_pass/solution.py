import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Brussels', 'Valencia'),
        ('Rome', 'Valencia'),
        ('Brussels', 'Geneva'),
        ('Rome', 'Geneva'),
        ('Dubrovnik', 'Geneva'),
        ('Valencia', 'Geneva'),
        ('Rome', 'Riga'),
        ('Geneva', 'Budapest'),
        ('Riga', 'Brussels'),
        ('Rome', 'Budapest'),
        ('Rome', 'Brussels'),
        ('Brussels', 'Budapest'),
        ('Dubrovnik', 'Rome')
    ]
    
    # Create adjacency list for flights
    adjacency = {city: set() for city in cities}
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)
    
    # Days: 1..17
    days = 17
    
    # Create Z3 variables: day[i] is the city visited on day i (1-based)
    day = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day variable must be a valid city index (0..6)
    for d in day:
        s.add(And(d >= 0, d <= 6))
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either same city or adjacent
        constraints = []
        for city_idx in range(len(cities)):
            city = cities[city_idx]
            adjacent_cities = adjacency[city]
            for adj_city in adjacent_cities:
                adj_idx = city_map[adj_city]
                constraints.append(And(current_city == city_idx, next_city == adj_idx))
            constraints.append(And(current_city == city_idx, next_city == city_idx))
        s.add(Or(constraints))
    
    # Duration constraints
    # Brussels: 5 days
    brussels_days = Sum([If(day[i] == city_map['Brussels'], 1, 0) for i in range(days)])
    s.add(brussels_days == 5)
    # Rome: 2 days
    rome_days = Sum([If(day[i] == city_map['Rome'], 1, 0) for i in range(days)])
    s.add(rome_days == 2)
    # Dubrovnik: 3 days
    dubrovnik_days = Sum([If(day[i] == city_map['Dubrovnik'], 1, 0) for i in range(days)])
    s.add(dubrovnik_days == 3)
    # Geneva: 5 days
    geneva_days = Sum([If(day[i] == city_map['Geneva'], 1, 0) for i in range(days)])
    s.add(geneva_days == 5)
    # Budapest: 2 days
    budapest_days = Sum([If(day[i] == city_map['Budapest'], 1, 0) for i in range(days)])
    s.add(budapest_days == 2)
    # Riga: 4 days
    riga_days = Sum([If(day[i] == city_map['Riga'], 1, 0) for i in range(days)])
    s.add(riga_days == 4)
    # Valencia: 2 days
    valencia_days = Sum([If(day[i] == city_map['Valencia'], 1, 0) for i in range(days)])
    s.add(valencia_days == 2)
    
    # Event constraints
    # Brussels workshop between day 7 and 11 (1-based, inclusive)
    s.add(Or([day[i] == city_map['Brussels'] for i in range(6, 11)]))
    
    # Budapest meeting between day 16 and 17 (indices 15-16)
    s.add(Or(day[15] == city_map['Budapest'], day[16] == city_map['Budapest']))
    
    # Riga friends between day 4 and 7 (indices 3-6)
    s.add(Or([day[i] == city_map['Riga'] for i in range(3, 7)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i + 1, 'place': cities[city_idx]})
        
        # Verify the solution meets all constraints
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        assert city_counts['Brussels'] == 5
        assert city_counts['Rome'] == 2
        assert city_counts['Dubrovnik'] == 3
        assert city_counts['Geneva'] == 5
        assert city_counts['Budapest'] == 2
        assert city_counts['Riga'] == 4
        assert city_counts['Valencia'] == 2
        
        # Check event constraints
        brussels_workshop = False
        for entry in itinerary:
            if entry['place'] == 'Brussels' and 7 <= entry['day'] <= 11:
                brussels_workshop = True
        assert brussels_workshop
        
        budapest_meeting = False
        for entry in itinerary:
            if entry['place'] == 'Budapest' and 16 <= entry['day'] <= 17:
                budapest_meeting = True
        assert budapest_meeting
        
        riga_meeting = False
        for entry in itinerary:
            if entry['place'] == 'Riga' and 4 <= entry['day'] <= 7:
                riga_meeting = True
        assert riga_meeting
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert next_place in adjacency[current], f"No flight from {current} to {next_place}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))