from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Manchester': ['Stuttgart', 'Madrid', 'Vienna'],
        'Stuttgart': ['Manchester', 'Vienna'],
        'Madrid': ['Manchester', 'Vienna'],
        'Vienna': ['Manchester', 'Stuttgart', 'Madrid']
    }
    
    # Create Z3 variables for each day (1..15)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    s = Solver()
    
    # Each day must be one of the cities (0..3)
    for day in days:
        s.add(And(day >= 0, day <= 3))
    
    # Manchester: 7 days, including days 1-7
    manchester_days = [If(days[i] == city_to_idx['Manchester'], 1, 0) for i in range(15)]
    s.add(sum(manchester_days) == 7)
    for i in range(7):  # days 1-7 (0-based 0..6)
        s.add(days[i] == city_to_idx['Manchester'])
    
    # Stuttgart: 5 days, workshop between days 11-15 (0-based 10..14)
    stuttgart_days = [If(days[i] == city_to_idx['Stuttgart'], 1, 0) for i in range(15)]
    s.add(sum(stuttgart_days) == 5)
    # At least one day in Stuttgart between days 11-15 (indices 10..14)
    s.add(Or([days[i] == city_to_idx['Stuttgart'] for i in range(10, 15)]))
    
    # Madrid: 4 days
    madrid_days = [If(days[i] == city_to_idx['Madrid'], 1, 0) for i in range(15)]
    s.add(sum(madrid_days) == 4)
    
    # Vienna: 2 days
    vienna_days = [If(days[i] == city_to_idx['Vienna'], 1, 0) for i in range(15)]
    s.add(sum(vienna_days) == 2)
    
    # Flight transitions: consecutive days can only change to directly connected cities
    for i in range(14):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
              for a in direct_flights 
              for b in direct_flights[a] if a != b]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
        for i in range(15):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            itinerary.append({'day': day_num, 'place': city_names[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Output the itinerary in JSON format
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No valid itinerary found.")

solve_itinerary()