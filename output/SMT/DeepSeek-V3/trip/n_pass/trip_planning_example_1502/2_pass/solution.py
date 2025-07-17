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
    
    # Direct flights as tuples (from, to)
    direct_flights = [
        (5, 4), (0, 2), (3, 1), (5, 3), (2, 1),
        (4, 6), (1, 4), (0, 4), (5, 1), (5, 2),
        (1, 8), (1, 9), (8, 9), (6, 7), (5, 8),
        (5, 9), (2, 3), (0, 5), (5, 6), (9, 7),
        (9, 4), (2, 4), (9, 6), (2, 9)
    ]
    # Make flights bidirectional
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create Z3 variables: assign a city to each day (1..27)
    day_city = [Int(f'day_{i}_city') for i in range(1, 28)]
    
    s = Solver()
    
    # Each day's city must be one of the 10 cities
    for day in day_city:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraints for required days in each city
    # Santorini: 3 days
    s.add(Sum([If(day == cities['Santorini'], 1, 0) for day in day_city]) == 3)
    # Valencia: 4 days
    s.add(Sum([If(day == cities['Valencia'], 1, 0) for day in day_city]) == 4)
    # Madrid: 2 days (but also must be present on days 6-7)
    s.add(Sum([If(day == cities['Madrid'], 1, 0) for day in day_city]) == 2)
    s.add(Or(day_city[5] == cities['Madrid'], day_city[6] == cities['Madrid']))
    # Seville: 2 days
    s.add(Sum([If(day == cities['Seville'], 1, 0) for day in day_city]) == 2)
    # Bucharest: 3 days
    s.add(Sum([If(day == cities['Bucharest'], 1, 0) for day in day_city]) == 3)
    # Vienna: 4 days, wedding between day 3 and 6 (days 3,4,5,6)
    s.add(Sum([If(day == cities['Vienna'], 1, 0) for day in day_city]) == 4)
    s.add(Or([day_city[2] == cities['Vienna'], day_city[3] == cities['Vienna'], 
              day_city[4] == cities['Vienna'], day_city[5] == cities['Vienna']]))
    # Riga: 4 days, conference between day 20-23 (days 20,21,22,23)
    s.add(Sum([If(day == cities['Riga'], 1, 0) for day in day_city]) == 4)
    s.add(Or([day_city[19] == cities['Riga'], day_city[20] == cities['Riga'],
              day_city[21] == cities['Riga'], day_city[22] == cities['Riga']]))
    # Tallinn: 5 days, workshop between day 23-27 (days 23,24,25,26,27)
    s.add(Sum([If(day == cities['Tallinn'], 1, 0) for day in day_city]) == 5)
    s.add(Or([day_city[22] == cities['Tallinn'], day_city[23] == cities['Tallinn'],
              day_city[24] == cities['Tallinn'], day_city[25] == cities['Tallinn'],
              day_city[26] == cities['Tallinn']]))
    # Krakow: 5 days, friends between day 11-15 (days 11,12,13,14,15)
    s.add(Sum([If(day == cities['Krakow'], 1, 0) for day in day_city]) == 5)
    s.add(Or([day_city[10] == cities['Krakow'], day_city[11] == cities['Krakow'],
              day_city[12] == cities['Krakow'], day_city[13] == cities['Krakow'],
              day_city[14] == cities['Krakow']]))
    # Frankfurt: 4 days
    s.add(Sum([If(day == cities['Frankfurt'], 1, 0) for day in day_city]) == 4)
    
    # Flight transitions: consecutive days must be same city or connected by a direct flight
    for i in range(26):
        current_day = day_city[i]
        next_day = day_city[i + 1]
        s.add(Or(
            current_day == next_day,  # same city
            *[(current_day == a) & (next_day == b) for a, b in all_flights]  # direct flight
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(27):
            day = i + 1
            city_code = m.evaluate(day_city[i]).as_long()
            city_name = city_names[city_code]
            itinerary.append({"day": day, "place": city_name})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))