from z3 import *

def solve_itinerary():
    s = Solver()

    # Days are 1-based indexed from 1 to 12
    days = 12
    city_names = {0: 'Naples', 1: 'Seville', 2: 'Milan'}

    # Variables: for each day, which city are we in?
    day_city = [Int(f'day_{d+1}_city') for d in range(days)]

    # Each day_city must be 0, 1, or 2
    for d in range(days):
        s.add(And(day_city[d] >= 0, day_city[d] <= 2))

    # Flight transitions: can only fly between connected cities
    # Connected pairs: Milan-Seville (2-1), Naples-Milan (0-2)
    for d in range(days - 1):
        current = day_city[d]
        next_day = day_city[d + 1]
        s.add(Or(
            current == next_day,  # no flight
            And(current == 2, next_day == 1),  # Milan -> Seville
            And(current == 1, next_day == 2),  # Seville -> Milan
            And(current == 0, next_day == 2),  # Naples -> Milan
            And(current == 2, next_day == 0)   # Milan -> Naples
        ))

    # Variables to track flight days
    flight_days = [Bool(f'flight_{d+1}') for d in range(days - 1)]
    for d in range(days - 1):
        s.add(flight_days[d] == (day_city[d] != day_city[d + 1]))

    # Total days per city (including flight days)
    naples_days = Sum([If(Or(day_city[d] == 0, 
                            And(d > 0, flight_days[d-1], day_city[d-1] == 0),
                            And(d < days-1, flight_days[d], day_city[d+1] == 0)), 1, 0) 
                      for d in range(days)])
    
    seville_days = Sum([If(Or(day_city[d] == 1, 
                             And(d > 0, flight_days[d-1], day_city[d-1] == 1),
                             And(d < days-1, flight_days[d], day_city[d+1] == 1)), 1, 0) 
                       for d in range(days)])
    
    milan_days = Sum([If(Or(day_city[d] == 2, 
                           And(d > 0, flight_days[d-1], day_city[d-1] == 2),
                           And(d < days-1, flight_days[d], day_city[d+1] == 2)), 1, 0) 
                     for d in range(days)])

    s.add(naples_days == 3)
    s.add(seville_days == 4)
    s.add(milan_days == 7)

    # Seville show constraint: days 9-12 (0-based 8..11) must be Seville
    for d in range(8, 12):
        s.add(day_city[d] == 1)
        # No flights during show days
        if d < 11:
            s.add(Not(flight_days[d]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(days):
            city_code = model.evaluate(day_city[d]).as_long()
            itinerary.append({'day': d + 1, 'city': city_names[city_code]})
        
        # Verify flight days are properly counted
        flight_days_count = sum(1 for d in range(days-1) if model.evaluate(flight_days[d]))
        print(f"Total flight days: {flight_days_count}")
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))