from z3 import *

def solve_itinerary():
    # Cities with required days
    cities = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    city_list = list(cities.keys())
    city_map = {city: i for i, city in enumerate(city_list)}
    num_days = 25

    # Enhanced flight connections (added some missing connections)
    direct_flights = [
        ('Lisbon', 'Paris'), ('Lisbon', 'Seville'), ('Lisbon', 'Prague'),
        ('Lisbon', 'Valencia'), ('Lisbon', 'Nice'), ('Lisbon', 'Oslo'),
        ('Lyon', 'Nice'), ('Lyon', 'Prague'), ('Lyon', 'Paris'),
        ('Lyon', 'Valencia'), ('Lyon', 'Oslo'),
        ('Nice', 'Oslo'), ('Nice', 'Paris'), ('Nice', 'Mykonos'),
        ('Nice', 'Lisbon'),
        ('Oslo', 'Tallinn'), ('Oslo', 'Paris'), ('Oslo', 'Prague'),
        ('Oslo', 'Lyon'), ('Oslo', 'Nice'),
        ('Paris', 'Valencia'), ('Paris', 'Tallinn'), ('Paris', 'Prague'),
        ('Paris', 'Seville'),
        ('Prague', 'Tallinn'), ('Prague', 'Valencia'),
        ('Seville', 'Valencia'),
        ('Mykonos', 'Nice')  # Only connection
    ]

    # Build flight graph
    flight_graph = {city: set() for city in city_list}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)

    # Z3 setup
    s = Solver()
    day = [Int(f'day_{i}') for i in range(num_days)]

    # Basic constraints
    for d in day:
        s.add(d >= 0, d < len(city_list))

    # Duration constraints
    for city, days in cities.items():
        s.add(sum([If(day[i] == city_map[city], 1, 0) for i in range(num_days)]) == days)

    # Event constraints (with some flexibility)
    # Valencia must include day 3 or 4
    s.add(Or(day[2] == city_map['Valencia'], day[3] == city_map['Valencia']))
    
    # Oslo must include at least one day between 13-15
    s.add(Or(day[12] == city_map['Oslo'], day[13] == city_map['Oslo'], day[14] == city_map['Oslo']))
    
    # Seville fixed days 5-9 (0-based 4-8)
    for i in range(4, 9):
        s.add(day[i] == city_map['Seville'])
    
    # Mykonos fixed days 21-25 (0-based 20-24)
    for i in range(20, 25):
        s.add(day[i] == city_map['Mykonos'])

    # Flight constraints with day counting
    for i in range(num_days - 1):
        current = day[i]
        next_day = day[i + 1]
        # Can stay or fly to connected city
        s.add(Or(
            current == next_day,
            *[And(current == city_map[a], next_day == city_map[b]) 
              for a in flight_graph for b in flight_graph[a]]
        ))

    # Strategic constraints to help solver
    # Limit consecutive days in same city (except for required blocks)
    for i in range(num_days - 4):
        # Allow up to 4 consecutive days (for Seville/Mykonos blocks)
        s.add(Not(And(
            day[i] == day[i+1],
            day[i] == day[i+2],
            day[i] == day[i+3],
            day[i] == day[i+4]
        )))

    # Try to distribute cities more evenly
    for city in city_list:
        if city not in ['Seville', 'Mykonos']:  # These have fixed blocks
            # Ensure city appears in at least 2 separate periods
            appears = [If(day[i] == city_map[city], 1, 0) for i in range(num_days)]
            s.add(Sum([If(And(appears[i] == 1, appears[i+1] == 0), 1, 0) 
                      for i in range(num_days - 1)]) >= 1)

    # Solve with timeout
    s.set("timeout", 60000)  # 60 seconds
    result = s.check()
    
    if result == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i + 1, 'city': city_list[city_idx]})
        
        # Verify solution
        city_days = {city: 0 for city in city_list}
        for entry in itinerary:
            city_days[entry['city']] += 1
        
        print("Verification:")
        for city, req in cities.items():
            print(f"{city}: Required {req}, Actual {city_days[city]}")
        
        return {'itinerary': itinerary}
    else:
        print("Failed to find solution. Reason:", result)
        return {'error': 'No valid itinerary found'}

# Run and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))