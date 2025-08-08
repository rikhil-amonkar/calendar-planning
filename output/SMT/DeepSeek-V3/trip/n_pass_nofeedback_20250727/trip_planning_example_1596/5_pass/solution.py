from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        'Budapest': ['Munich', 'Vienna', 'Warsaw', 'Bucharest', 'Edinburgh', 'Barcelona'],
        'Bucharest': ['Riga', 'Munich', 'Warsaw', 'Vienna', 'Budapest', 'Barcelona'],
        'Munich': ['Budapest', 'Krakow', 'Warsaw', 'Bucharest', 'Barcelona', 'Stockholm', 'Edinburgh', 'Vienna', 'Riga'],
        'Krakow': ['Munich', 'Warsaw', 'Edinburgh', 'Stockholm', 'Vienna', 'Barcelona'],
        'Barcelona': ['Warsaw', 'Munich', 'Stockholm', 'Riga', 'Edinburgh', 'Budapest', 'Krakow', 'Bucharest', 'Vienna'],
        'Warsaw': ['Munich', 'Krakow', 'Barcelona', 'Bucharest', 'Budapest', 'Vienna', 'Riga', 'Stockholm'],
        'Stockholm': ['Edinburgh', 'Krakow', 'Munich', 'Barcelona', 'Riga', 'Vienna', 'Warsaw'],
        'Riga': ['Bucharest', 'Barcelona', 'Vienna', 'Munich', 'Warsaw', 'Stockholm', 'Edinburgh'],
        'Edinburgh': ['Stockholm', 'Krakow', 'Barcelona', 'Budapest', 'Munich', 'Riga'],
        'Vienna': ['Budapest', 'Krakow', 'Bucharest', 'Warsaw', 'Stockholm', 'Riga', 'Munich', 'Barcelona']
    }
    
    # Fixed events
    fixed_events = {
        18: 'Munich', 19: 'Munich', 20: 'Munich',
        25: 'Warsaw', 26: 'Warsaw', 27: 'Warsaw', 28: 'Warsaw', 29: 'Warsaw',
        9: 'Budapest', 10: 'Budapest', 11: 'Budapest', 12: 'Budapest', 13: 'Budapest',
        17: 'Stockholm',  # Day 17: Stockholm
        1: 'Edinburgh', 2: 'Edinburgh', 3: 'Edinburgh', 4: 'Edinburgh', 5: 'Edinburgh'
    }
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each day (1-32)
    day_vars = [Int(f'day_{day}') for day in range(1, 33)]
    
    # Assign city codes to integers
    city_codes = {city: idx for idx, city in enumerate(cities.keys())}
    code_to_city = {idx: city for city, idx in city_codes.items()}
    
    # Add constraints for fixed events
    for day, city in fixed_events.items():
        s.add(day_vars[day-1] == city_codes[city])
    
    # Flight transitions: consecutive days must be either same city or connected by direct flight
    for day in range(31):  # days 1-31 (since we look at day+1)
        current = day_vars[day]
        next_day = day_vars[day+1]
        
        # Generate all possible valid transitions
        valid_transitions = []
        for city in cities:
            for neighbor in direct_flights[city]:
                valid_transitions.append(And(current == city_codes[city], next_day == city_codes[neighbor]))
        
        # Either stay in same city or use a valid flight
        s.add(Or(current == next_day, *valid_transitions))
    
    # Ensure each city's total days meet the required stays
    for city, days in cities.items():
        city_code = city_codes[city]
        total = 0
        for day in range(32):
            total += If(day_vars[day] == city_code, 1, 0)
        s.add(total == days)
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(32):
            city_code = m.evaluate(day_vars[day]).as_long()
            itinerary.append({'day': day+1, 'place': code_to_city[city_code]})
        
        # Verify the solution
        # Check fixed events
        for day, city in fixed_events.items():
            if itinerary[day-1]['place'] != city:
                print(f"Error: Day {day} should be in {city} but is in {itinerary[day-1]['place']}")
                return None
        
        # Check flight connections
        for i in range(31):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p and next_p not in direct_flights[current]:
                print(f"Error: No direct flight from {current} to {next_p} on day {i+2}")
                return None
        
        # Check stay durations
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        for city, count in city_counts.items():
            if count != cities[city]:
                print(f"Error: {city} has {count} days but needs {cities[city]}")
                return None
        
        return {'itinerary': itinerary}
    else:
        print("No valid itinerary found")
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))