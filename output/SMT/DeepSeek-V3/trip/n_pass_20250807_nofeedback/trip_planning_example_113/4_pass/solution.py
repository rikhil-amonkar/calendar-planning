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

    # Total days per city (including flight days)
    naples_days = Sum([If(day_city[d] == 0, 1, 0) for d in range(days)])
    seville_days = Sum([If(day_city[d] == 1, 1, 0) for d in range(days)])
    milan_days = Sum([If(day_city[d] == 2, 1, 0) for d in range(days)])

    s.add(naples_days == 3)
    s.add(seville_days == 4)
    s.add(milan_days == 7)

    # Seville show constraint: days 9-12 (0-based 8..11) must be Seville
    for d in range(8, 12):
        s.add(day_city[d] == 1)

    # Additional constraint: cannot be in two different cities on the same day
    # (except for flight days which are handled by counting for both)
    # This is already handled by having one city per day in day_city

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(days):
            city_code = model.evaluate(day_city[d]).as_long()
            itinerary.append({'day': d + 1, 'city': city_names[city_code]})
        
        # Verify the solution meets all requirements
        naples_count = sum(1 for day in itinerary if day['city'] == 'Naples')
        seville_count = sum(1 for day in itinerary if day['city'] == 'Seville')
        milan_count = sum(1 for day in itinerary if day['city'] == 'Milan')
        
        assert naples_count == 3, f"Naples days: {naples_count} (expected 3)"
        assert seville_count == 4, f"Seville days: {seville_count} (expected 4)"
        assert milan_count == 7, f"Milan days: {milan_count} (expected 7)"
        assert all(day['city'] == 'Seville' for day in itinerary[8:12]), "Seville show days not correct"
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))