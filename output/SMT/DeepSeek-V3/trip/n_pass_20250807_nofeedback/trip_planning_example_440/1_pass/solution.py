from z3 import *

def solve_itinerary():
    # Cities
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    city_names = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
    n_cities = len(cities)
    
    # Direct flights: adjacency list
    direct_flights = {
        'Split': ['Helsinki', 'Geneva', 'Vilnius'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Geneva': ['Split', 'Helsinki'],
        'Vilnius': ['Helsinki', 'Split'],
        'Reykjavik': ['Helsinki']
    }
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: each day is assigned a city (0 to n_cities-1)
    days = [Int(f'day_{i}') for i in range(1, 13)]
    for day in days:
        s.add(day >= 0, day < n_cities)
    
    # Constraints for city stays
    # Total days per city
    split_days = Sum([If(day == cities['Split'], 1, 0) for day in days])
    helsinki_days = Sum([If(day == cities['Helsinki'], 1, 0) for day in days])
    reykjavik_days = Sum([If(day == cities['Reykjavik'], 1, 0) for day in days])
    vilnius_days = Sum([If(day == cities['Vilnius'], 1, 0) for day in days])
    geneva_days = Sum([If(day == cities['Geneva'], 1, 0) for day in days])
    
    s.add(split_days == 2)
    s.add(helsinki_days == 2)
    s.add(reykjavik_days == 3)
    s.add(vilnius_days == 3)
    s.add(geneva_days == 6)
    
    # Fixed date constraints
    # Reykjavik between day 10-12 (days are 1-based in problem, 0-based here)
    s.add(days[9] == cities['Reykjavik'])  # day 10
    s.add(days[10] == cities['Reykjavik'])  # day 11
    s.add(days[11] == cities['Reykjavik'])  # day 12
    
    # Vilnius between day 7-9 (days 6-8 in 0-based)
    s.add(days[6] == cities['Vilnius'])  # day 7
    s.add(days[7] == cities['Vilnius'])  # day 8
    s.add(days[8] == cities['Vilnius'])  # day 9
    
    # Flight transitions: consecutive days can only be same city or connected by direct flight
    for i in range(11):  # days 1-11 to days 2-12
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            # Check all possible direct flights
            *[
                And(current_day == cities[city], next_day == cities[neighbor])
                for city in direct_flights
                for neighbor in direct_flights[city]
            ]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_val = m.evaluate(days[i]).as_long()
            city = city_names[city_val]
            itinerary.append({'day': day_num, 'place': city})
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))