from z3 import *

def solve_itinerary():
    # Cities and their IDs
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_ids = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split')
    ]
    
    # Correct any typos in flight names
    corrected_flights = []
    for src, dst in direct_flights:
        if src == 'Munich':
            src = 'Munich'
        if dst == 'Munich':
            dst = 'Munich'
        if src == 'Porto':
            src = 'Porto'
        if dst == 'Porto':
            dst = 'Porto'
        if src == 'Krakow':
            src = 'Krakow'
        if dst == 'Krakow':
            dst = 'Krakow'
        corrected_flights.append((src, dst))
    direct_flights = corrected_flights
    
    # Create a Z3 solver
    s = Solver()
    
    # Day variables: day[i] represents the city on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 17)]
    
    # Constraints for each day to be one of the cities
    for day in days:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraints for transitions: consecutive days must be same city or have a direct flight
    for i in range(1, 16):
        current_city = days[i-1]
        next_city = days[i]
        s.add(Or(
            current_city == next_city,
            Or([
                And(current_city == city_ids[src], next_city == city_ids[dst])
                for src, dst in direct_flights
            ] + [
                And(current_city == city_ids[dst], next_city == city_ids[src])
                for src, dst in direct_flights
            ])
        ))
    
    # Duration constraints for each city
    city_durations = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    for city in cities:
        total = Sum([If(days[i] == city_ids[city], 1, 0) for i in range(16)])
        s.add(total == city_durations[city])
    
    # Event constraints:
    # Wedding in Milan between day 11-13 (days 10..12 in 0-based)
    for i in [10, 11, 12]:
        s.add(days[i] == city_ids['Milan'])
    
    # Friends in Krakow between day 8-9 (days 7..8 in 0-based)
    s.add(Or(days[7] == city_ids['Krakow'], days[8] == city_ids['Krakow']))
    
    # Show in Munich between day 4-8 (days 3..7 in 0-based)
    for i in [3, 4, 5, 6, 7]:
        s.add(days[i] == city_ids['Munich'])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 17):
            city_id = model.evaluate(days[i-1]).as_long()
            city = cities[city_id]
            itinerary.append({'day': i, 'place': city})
        
        # Verify the solution meets all constraints
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        for city in city_durations:
            assert city_counts[city] == city_durations[city], f"Duration mismatch for {city}"
        
        for i in range(1, 16):
            current = itinerary[i-1]['place']
            next_place = itinerary[i]['place']
            if current != next_place:
                assert (current, next_place) in direct_flights or (next_place, current) in direct_flights, \
                    f"Invalid flight from {current} to {next_place} on day {i+1}"
        
        assert itinerary[10]['place'] == 'Milan'  # day 11
        assert itinerary[11]['place'] == 'Milan'  # day 12
        assert itinerary[12]['place'] == 'Milan'  # day 13
        
        assert (itinerary[7]['place'] == 'Krakow' or itinerary[8]['place'] == 'Krakow')
        
        for i in range(3, 8):
            assert itinerary[i]['place'] == 'Munich'
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")