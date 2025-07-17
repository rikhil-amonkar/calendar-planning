from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Santorini': 0,
        'Valencia': 1,
        'Madrid': 2,
        'Seville': 3,
        'Bucharest': 4,
        'Vienna': 5,
        'Riga': 6,
        'Tallinn': 7,
        'Krakow': 8,
        'Frankfurt': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights (bidirectional)
    direct_flights = [
        (5, 4), (0, 2), (3, 1), (5, 3), (2, 1),
        (4, 6), (1, 4), (0, 4), (5, 1), (5, 2),
        (1, 8), (1, 9), (8, 9), (6, 7), (5, 8),
        (5, 9), (2, 3), (0, 5), (5, 6), (9, 7),
        (9, 4), (2, 4), (9, 6), (2, 9)
    ]
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create solver and variables
    s = Solver()
    day_city = [Int(f'day_{i}') for i in range(1, 28)]
    
    # Each day must be one of the cities
    for day in day_city:
        s.add(Or([day == c for c in cities.values()]))
    
    # City day constraints
    def count_days(city_code):
        return Sum([If(day == city_code, 1, 0) for day in day_city])
    
    s.add(count_days(cities['Santorini']) == 3)
    s.add(count_days(cities['Valencia']) == 4)
    s.add(count_days(cities['Madrid']) == 2)
    s.add(count_days(cities['Seville']) == 2)
    s.add(count_days(cities['Bucharest']) == 3)
    s.add(count_days(cities['Vienna']) == 4)
    s.add(count_days(cities['Riga']) == 4)
    s.add(count_days(cities['Tallinn']) == 5)
    s.add(count_days(cities['Krakow']) == 5)
    s.add(count_days(cities['Frankfurt']) == 4)
    
    # Event constraints
    # Madrid days 6-7
    s.add(Or(day_city[5] == cities['Madrid'], day_city[6] == cities['Madrid']))
    # Vienna wedding days 3-6
    s.add(Or([day_city[i] == cities['Vienna'] for i in range(2, 6)]))
    # Riga conference days 20-23
    s.add(Or([day_city[i] == cities['Riga'] for i in range(19, 23)]))
    # Tallinn workshop days 23-27
    s.add(Or([day_city[i] == cities['Tallinn'] for i in range(22, 27)]))
    # Krakow friends days 11-15
    s.add(Or([day_city[i] == cities['Krakow'] for i in range(10, 15)]))
    
    # Flight transitions
    for i in range(26):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) for a, b in all_flights]
        ))
    
    # Solve and format output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(27):
            day_num = i + 1
            city_code = m.evaluate(day_city[i]).as_long()
            itinerary.append({"day": day_num, "place": city_names[city_code]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
import json
print(json.dumps(solve_itinerary(), indent=2))