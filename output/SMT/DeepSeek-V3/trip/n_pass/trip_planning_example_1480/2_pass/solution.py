from z3 import *

def solve_itinerary():
    # Cities and their codes for easier reference
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
    
    # Direct flights as adjacency list
    direct_flights = {
        0: [1, 5, 3, 7, 6],  # Geneva to Vienna, Madrid, Munich, Istanbul, Brussels
        1: [3, 9, 7, 8, 6, 4, 2, 5],  # Vienna to Munich, Vilnius, Istanbul, Riga, Brussels, Reykjavik, Venice, Madrid
        2: [6, 3, 5, 1, 7],  # Venice to Brussels, Munich, Madrid, Vienna, Istanbul
        3: [1, 4, 5, 2, 7, 6, 8, 9],  # Munich to Vienna, Reykjavik, Madrid, Venice, Istanbul, Brussels, Riga, Vilnius
        4: [5, 6, 1, 3],  # Reykjavik to Madrid, Brussels, Vienna, Munich
        5: [3, 2, 1, 6, 7, 0],  # Madrid to Munich, Venice, Vienna, Brussels, Istanbul, Geneva
        6: [7, 2, 8, 4, 1, 9, 0, 3, 5],  # Brussels to Istanbul, Venice, Riga, Reykjavik, Vienna, Vilnius, Geneva, Munich, Madrid
        7: [6, 0, 1, 8, 2, 9, 3],  # Istanbul to Brussels, Geneva, Vienna, Riga, Venice, Vilnius, Munich
        8: [6, 7, 1, 3, 9],  # Riga to Brussels, Istanbul, Vienna, Munich, Vilnius
        9: [1, 6, 7, 3, 8]   # Vilnius to Vienna, Brussels, Istanbul, Munich, Riga
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..27)
    days = [Int(f'day_{i}') for i in range(27)]
    
    s = Solver()
    
    # Each day must be one of the cities
    for d in days:
        s.add(Or([d == c for c in cities.values()]))
    
    # Fixed constraints:
    # Geneva between day 1-4
    for i in range(0, 4):
        s.add(days[i] == cities['Geneva'])
    
    # Venice workshop between day 7-11 (indices 6-10)
    for i in range(6, 11):
        s.add(days[i] == cities['Venice'])
    
    # Vilnius friends between day 20-23 (indices 19-22)
    for i in range(19, 23):
        s.add(days[i] == cities['Vilnius'])
    
    # Brussels wedding on day 26-27 (indices 25-26)
    s.add(days[25] == cities['Brussels'])
    s.add(days[26] == cities['Brussels'])
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(26):
        current_city = days[i]
        next_city = days[i+1]
        s.add(Or(current_city == next_city, 
                 And(current_city != next_city, 
                     Or([next_city == dst for dst in direct_flights[current_city.as_long()]]))))
    
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
    
    # Check and get model
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

# Generate and print the itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))