from z3 import *

def solve_scheduling():
    # Cities
    cities = {
        'Frankfurt': 0,
        'Manchester': 1,
        'Valencia': 2,
        'Naples': 3,
        'Oslo': 4,
        'Vilnius': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 4, 5],  # Frankfurt
        1: [0, 3, 4],        # Manchester
        2: [0, 3],           # Valencia
        3: [0, 1, 2, 4],     # Naples
        4: [0, 3, 5, 1],     # Oslo
        5: [0, 4]            # Vilnius
    }
    
    # Create Z3 variables for each day (1..16)
    days = [Int(f'day_{i}') for i in range(1, 17)]
    
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Transition constraints: consecutive days must be same city or connected by direct flight
    for i in range(len(days) - 1):
        current_day = days[i]
        next_day = days[i + 1]
        s.add(Or(
            current_day == next_day,
            *[And(current_day == c, next_day == n) for c in cities.values() for n in direct_flights[c]]
        ))
    
    # Fixed constraints:
    # Days 13-16 in Frankfurt
    for i in range(12, 16):
        s.add(days[i] == cities['Frankfurt'])
    
    # Wedding in Vilnius between day 12 and 13. So day 12 must be Vilnius (since day 13 is Frankfurt)
    s.add(days[11] == cities['Vilnius'])
    
    # Duration constraints:
    # Frankfurt: 4 days total (including the days 13-16)
    # So other days in Frankfurt must be 0 (since 13-16 is 4 days)
    s.add(Sum([If(days[i] == cities['Frankfurt'], 1, 0) for i in range(16)]) == 4)
    
    # Manchester: 4 days
    s.add(Sum([If(days[i] == cities['Manchester'], 1, 0) for i in range(16)]) == 4)
    
    # Valencia: 4 days
    s.add(Sum([If(days[i] == cities['Valencia'], 1, 0) for i in range(16)]) == 4)
    
    # Naples: 4 days
    s.add(Sum([If(days[i] == cities['Naples'], 1, 0) for i in range(16)]) == 4)
    
    # Oslo: 3 days
    s.add(Sum([If(days[i] == cities['Oslo'], 1, 0) for i in range(16)]) == 3)
    
    # Vilnius: 2 days (day 12 is one, so one more day)
    s.add(Sum([If(days[i] == cities['Vilnius'], 1, 0) for i in range(16)]) == 2)
    
    # Additional constraints to ensure the schedule is feasible
    # For example, ensure that the days before the fixed days are properly connected
    # Day 11 must be connected to Vilnius (day 12)
    s.add(Or(
        days[10] == cities['Vilnius'],
        *[And(days[10] == c, cities['Vilnius'] in direct_flights[c]) for c in cities.values() if c != cities['Vilnius']]
    ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(16):
            day_num = i + 1
            city_code = m.evaluate(days[i]).as_long()
            city = city_names[city_code]
            itinerary.append({'day': day_num, 'place': city})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_scheduling()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")