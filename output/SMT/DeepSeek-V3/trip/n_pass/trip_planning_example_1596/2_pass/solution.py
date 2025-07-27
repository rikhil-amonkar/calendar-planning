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
    
    # Initialize Z3 variables
    day_to_city = {day: Int(f'day_{day}') for day in range(1, 33)}
    
    s = Solver()
    
    # Assign city codes to integers
    city_codes = {city: idx for idx, city in enumerate(cities.keys())}
    code_to_city = {idx: city for city, idx in city_codes.items()}
    
    # Add constraints for fixed events
    for day, city in fixed_events.items():
        s.add(day_to_city[day] == city_codes[city])
    
    # Flight transitions: consecutive days must be either same city or connected by direct flight
    for day in range(1, 32):
        current_city = day_to_city[day]
        next_city = day_to_city[day + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_codes[a], next_city == city_codes[b]) 
              for a in cities for b in direct_flights[a]]
        ))
    
    # Ensure each city's total days meet the required stays
    for city in cities:
        city_code = city_codes[city]
        total_days = Sum([If(day_to_city[day] == city_code, 1, 0) for day in range(1, 33)])
        s.add(total_days == cities[city])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 33):
            city_code = m.evaluate(day_to_city[day]).as_long()
            itinerary.append({'day': day, 'place': code_to_city[city_code]})
        
        # Verify no impossible transitions
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i + 1]['place']
            if current != next_p and next_p not in direct_flights[current]:
                print(f"Invalid transition from {current} to {next_p} on day {itinerary[i]['day'] + 1}")
                return None
        
        # Verify fixed events
        for day, city in fixed_events.items():
            if itinerary[day - 1]['place'] != city:
                print(f"Fixed event violation on day {day}: expected {city}, got {itinerary[day - 1]['place']}")
                return None
        
        # Verify total days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        for city in cities:
            if city_days[city] != cities[city]:
                print(f"City {city} has {city_days[city]} days, expected {cities[city]}")
                return None
        
        return {'itinerary': itinerary}
    else:
        print("No solution found")
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))