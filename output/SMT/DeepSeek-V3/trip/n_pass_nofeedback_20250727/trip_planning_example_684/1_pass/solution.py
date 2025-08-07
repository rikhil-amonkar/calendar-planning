from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Amsterdam': 0,
        'Edinburgh': 1,
        'Brussels': 2,
        'Vienna': 3,
        'Berlin': 4,
        'Reykjavik': 5
    }
    inv_cities = {v: k for k, v in cities.items()}
    
    # Direct flights: list of tuples (city1, city2)
    direct_flights = [
        (1, 4),  # Edinburgh and Berlin
        (0, 4),   # Amsterdam and Berlin
        (1, 0),    # Edinburgh and Amsterdam
        (3, 4),    # Vienna and Berlin
        (4, 2),    # Berlin and Brussels
        (3, 5),    # Vienna and Reykjavik
        (1, 2),    # Edinburgh and Brussels
        (3, 2),    # Vienna and Brussels
        (0, 5),    # Amsterdam and Reykjavik
        (5, 2),    # Reykjavik and Brussels
        (0, 3),    # Amsterdam and Vienna
        (5, 4)     # Reykjavik and Berlin
    ]
    # Make flights bidirectional
    bidirectional_flights = direct_flights + [(b, a) for (a, b) in direct_flights]
    
    # Total days
    total_days = 23
    
    # Create Z3 variables for each day's city
    day_city = [Int(f'day_{i}_city') for i in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each day's city must be one of the 6 cities
    for day in range(total_days):
        s.add(Or([day_city[day] == cities[c] for c in cities]))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for day in range(total_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == a, next_city == b) for (a, b) in bidirectional_flights])
        ))
    
    # Duration constraints
    # Amsterdam: 4 days, including days 5-8 (days 5,6,7,8 in 1-based)
    amsterdam_days = [And(day_city[i] == cities['Amsterdam']) for i in [4,5,6,7]]  # 0-based days 4-7 (1-based 5-8)
    s.add(And(amsterdam_days))
    s.add(Sum([If(day_city[i] == cities['Amsterdam'], 1, 0) for i in range(total_days)]) == 4)
    
    # Edinburgh: 5 days
    s.add(Sum([If(day_city[i] == cities['Edinburgh'], 1, 0) for i in range(total_days)]) == 5)
    
    # Brussels: 5 days
    s.add(Sum([If(day_city[i] == cities['Brussels'], 1, 0) for i in range(total_days)]) == 5)
    
    # Vienna: 5 days
    s.add(Sum([If(day_city[i] == cities['Vienna'], 1, 0) for i in range(total_days)]) == 5)
    
    # Berlin: 4 days, including days 16-19 (1-based days 16,17,18,19 → 0-based 15,16,17,18)
    berlin_days = [And(day_city[i] == cities['Berlin']) for i in [15,16,17,18]]
    s.add(And(berlin_days))
    s.add(Sum([If(day_city[i] == cities['Berlin'], 1, 0) for i in range(total_days)]) == 4)
    
    # Reykjavik: 5 days, including days 12-16 (1-based days 12,13,14,15,16 → 0-based 11,12,13,14,15)
    reykjavik_days = [And(day_city[i] == cities['Reykjavik']) for i in [11,12,13,14,15]]
    s.add(And(reykjavik_days))
    s.add(Sum([If(day_city[i] == cities['Reykjavik'], 1, 0) for i in range(total_days)]) == 5)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(total_days):
            city_code = m.evaluate(day_city[day]).as_long()
            city_name = inv_cities[city_code]
            itinerary.append({"day": day + 1, "place": city_name})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))