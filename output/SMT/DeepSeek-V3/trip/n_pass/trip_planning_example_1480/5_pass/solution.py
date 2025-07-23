from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Geneva': 0,
        'Vienna': 1,
        'Venice': 2,
        'Munich': 3,
        'Reykjavik': 4,
        'Madrid': 5,
        'Brussels': 6,
        'Istanbul': 7,
        'Riga': 8,
        'Vilnius': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights (bidirectional)
    direct_flights = {
        0: [1, 5, 3, 7, 6],  # Geneva
        1: [0, 3, 9, 7, 8, 6, 4, 2, 5],  # Vienna
        2: [6, 3, 5, 1, 7],  # Venice
        3: [0, 1, 4, 5, 2, 7, 6, 8, 9],  # Munich
        4: [5, 6, 1, 3],  # Reykjavik
        5: [0, 3, 2, 1, 6, 7],  # Madrid
        6: [0, 1, 2, 3, 4, 7, 8, 9, 5],  # Brussels
        7: [0, 1, 2, 3, 6, 8, 9],  # Istanbul
        8: [1, 3, 6, 7, 9],  # Riga
        9: [1, 3, 6, 7, 8]   # Vilnius
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(27)]
    s = Solver()
    
    # Each day must be one of the cities
    for d in days:
        s.add(Or([d == c for c in cities.values()]))
    
    # Fixed constraints:
    # Geneva days 1-4
    for i in range(0, 4):
        s.add(days[i] == cities['Geneva'])
    
    # Venice workshop days 7-11
    for i in range(6, 11):
        s.add(days[i] == cities['Venice'])
    
    # Vilnius friends days 20-23
    for i in range(19, 23):
        s.add(days[i] == cities['Vilnius'])
    
    # Brussels wedding days 26-27
    s.add(days[25] == cities['Brussels'])
    s.add(days[26] == cities['Brussels'])
    
    # Flight transitions between consecutive days
    for i in range(26):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take a direct flight
        s.add(Or(current == next_day, 
                And([Implies(current == city, Or([next_day == dst for dst in direct_flights[city]]))
                    for city in cities.values()])))
    
    # Total days per city (including overlaps)
    total_days = {
        'Geneva': 4,
        'Vienna': 4,
        'Venice': 5,
        'Munich': 5,
        'Reykjavik': 2,
        'Madrid': 4,
        'Brussels': 2,
        'Istanbul': 4,
        'Riga': 2,
        'Vilnius': 4
    }
    
    for city, total in total_days.items():
        city_code = cities[city]
        s.add(Sum([If(d == city_code, 1, 0) for d in days]) == total)
    
    # Find solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(27):
            day_num = i + 1
            city_code = m.eval(days[i]).as_long()
            city_name = city_names[city_code]
            itinerary.append({"day": day_num, "place": city_name})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))