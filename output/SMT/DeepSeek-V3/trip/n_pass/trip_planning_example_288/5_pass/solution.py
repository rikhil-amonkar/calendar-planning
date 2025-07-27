from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = {
        0: [1, 2, 3],  # Manchester
        1: [0, 3],      # Stuttgart
        2: [0, 3],       # Madrid
        3: [0, 1, 2]     # Vienna
    }
    
    # Create solver and day variables
    s = Solver()
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Each day must be one of the cities (0-3)
    for day in days:
        s.add(And(day >= 0, day <= 3))
    
    # Manchester: Days 1-7 (indices 0-6)
    for i in range(7):
        s.add(days[i] == city_to_idx['Manchester'])
    
    # Stuttgart: At least one day between 11-15 (indices 10-14)
    s.add(Or([days[i] == city_to_idx['Stuttgart'] for i in range(10, 15)]))
    
    # Total days constraints
    def count_days(city_idx):
        return Sum([If(days[i] == city_idx, 1, 0) for i in range(15)])
    
    s.add(count_days(city_to_idx['Manchester']) == 7)
    s.add(count_days(city_to_idx['Stuttgart']) == 5)
    s.add(count_days(city_to_idx['Madrid']) == 4)
    s.add(count_days(city_to_idx['Vienna']) == 2)
    
    # Flight transitions
    for i in range(14):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == a, next_day == b) 
              for a in range(4) 
              for b in direct_flights[a]]
        ))
    
    # Solve and format output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(15):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            itinerary.append({'day': day_num, 'place': cities[city_idx]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Output JSON
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No valid itinerary found.")

solve_itinerary()