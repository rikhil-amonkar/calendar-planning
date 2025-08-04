from z3 import *
import json

def solve_itinerary():
    # Cities and their mappings
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ('Berlin', 'Tallinn'),
        ('Prague', 'Tallinn'),
        ('Stockholm', 'Tallinn'),
        ('Prague', 'Stockholm'),
        ('Stockholm', 'Berlin')
    ]
    
    # Create solver
    s = Solver()
    
    # Day variables (1-12)
    days = [Int(f'day_{i}') for i in range(1, 13)]
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == city_map[city] for city in cities]))
    
    # Total days constraints
    s.add(Sum([If(day == city_map['Prague'], 1, 0) for day in days]) == 2)
    s.add(Sum([If(day == city_map['Berlin'], 1, 0) for day in days]) == 3)
    s.add(Sum([If(day == city_map['Tallinn'], 1, 0) for day in days]) == 5)
    s.add(Sum([If(day == city_map['Stockholm'], 1, 0) for day in days]) == 5)
    
    # Specific day constraints
    s.add(days[5] == city_map['Berlin'])  # Day 6
    s.add(days[7] == city_map['Berlin'])  # Day 8
    
    # Tallinn between days 8-12 (indices 7-11)
    for i in range(7, 12):
        s.add(days[i] == city_map['Tallinn'])
    
    # Flight transitions
    flight_pairs = [(city_map[a], city_map[b]) for a, b in direct_flights]
    flight_pairs += [(b, a) for a, b in direct_flights]  # Add reverse directions
    
    for i in range(11):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == a, next_day == b) for (a, b) in flight_pairs])
        ))
    
    # Additional constraint: Must start somewhere (not strictly needed but helps)
    s.add(Or([days[0] == city_map[city] for city in cities]))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify specific days
        assert itinerary[5]['place'] == 'Berlin'  # Day 6
        assert itinerary[7]['place'] == 'Berlin'  # Day 8
        for i in range(7, 12):
            assert itinerary[i]['place'] == 'Tallinn'
        
        # Verify flight connections
        for i in range(11):
            current = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current != next_city:
                assert (current, next_city) in direct_flights or (next_city, current) in direct_flights
        
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found."}, indent=2)

print(solve_itinerary())