import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: bidirectional
    direct_flights = [
        ('Lisbon', 'Bucharest'),
        ('Berlin', 'Lisbon'),
        ('Bucharest', 'Riga'),
        ('Berlin', 'Riga'),
        ('Split', 'Lyon'),
        ('Lisbon', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Berlin', 'Split'),
        ('Lyon', 'Lisbon'),
        ('Berlin', 'Tallinn'),
        ('Lyon', 'Bucharest')
    ]
    # Create a flight graph (undirected)
    flight_graph = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Total days
    total_days = 22
    
    # Create Z3 variables: for each day, which city are you in?
    # day is 1-based
    assignments = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each assignment must be between 0 and 6 (indices of cities)
    for day in assignments:
        s.add(day >= 0, day < len(cities))
    
    # Duration constraints for each city
    durations = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }
    
    # Fixed events:
    # Berlin from day 1 to 5
    for day in range(1, 6):
        s.add(assignments[day - 1] == city_map['Berlin'])
    
    # Bucharest between day 13 and 15 (inclusive)
    s.add(assignments[12] == city_map['Bucharest'])  # day 13
    s.add(assignments[13] == city_map['Bucharest'])  # day 14
    s.add(assignments[14] == city_map['Bucharest'])  # day 15
    
    # Lyon between day 7 and 11 for wedding (5 days)
    for day in range(7, 12):
        s.add(assignments[day - 1] == city_map['Lyon'])
    
    # Now, ensure the total days per city.
    for city in cities:
        count = durations[city]
        s.add(Sum([If(assignments[i] == city_map[city], 1, 0) for i in range(total_days)]) == count)
    
    # Flight transitions: if day i and i+1 are different cities, there must be a flight between them.
    for i in range(total_days - 1):
        current_day_city = assignments[i]
        next_day_city = assignments[i + 1]
        # If cities are different, check flight exists.
        s.add(Implies(
            current_day_city != next_day_city,
            Or([And(current_day_city == city_map[a], next_day_city == city_map[b]) 
                for a, b in direct_flights] + 
               [And(current_day_city == city_map[b], next_day_city == city_map[a]) 
                for a, b in direct_flights])
        ))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, total_days + 1):
            city_idx = m.evaluate(assignments[day - 1]).as_long()
            itinerary.append({'day': day, 'city': cities[city_idx]})
        
        # Verify durations
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['city']] += 1
        for city in cities:
            assert city_days[city] == durations[city], f"City {city} has {city_days[city]} days, expected {durations[city]}"
        
        # Verify flights
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if current_city != next_city:
                assert next_city in flight_graph[current_city], f"No flight from {current_city} to {next_city}"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")