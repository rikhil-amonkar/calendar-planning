from z3 import *

def solve_trip_planning():
    s = Solver()

    # Days are 1..12
    days = range(1, 13)
    cities = ['Naples', 'Seville', 'Milan']
    city_num = {c: i for i, c in enumerate(cities)}

    # Decision variables for each day's city
    day_city = [Int(f'day_{day}_city') for day in days]
    for dc in day_city:
        s.add(dc >= 0, dc <= 2)  # 0=Naples, 1=Seville, 2=Milan

    # Days 9-12 must be in Seville
    for day in range(9, 13):
        s.add(day_city[day-1] == city_num['Seville'])

    # Flight constraints - can only move between connected cities
    for i in range(len(days)-1):
        current = day_city[i]
        next_c = day_city[i+1]
        s.add(Or(
            current == next_c,  # Stay in same city
            # Naples <-> Milan
            And(current == city_num['Naples'], next_c == city_num['Milan']),
            And(current == city_num['Milan'], next_c == city_num['Naples']),
            # Milan <-> Seville
            And(current == city_num['Milan'], next_c == city_num['Seville']),
            And(current == city_num['Seville'], next_c == city_num['Milan'])
        ))

    # Count days in each city (including flight days)
    naples_days = Sum([If(dc == city_num['Naples'], 1, 0) for dc in day_city])
    seville_days = Sum([If(dc == city_num['Seville'], 1, 0) for dc in day_city])
    milan_days = Sum([If(dc == city_num['Milan'], 1, 0) for dc in day_city])

    s.add(naples_days == 3)
    s.add(seville_days == 4)  # Exactly 4 days (all in 9-12)
    s.add(milan_days == 7)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in days:
            city_val = model.evaluate(day_city[day-1]).as_long()
            itinerary.append({'day': day, 'place': cities[city_val]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_trip_planning()
import json
print(json.dumps(result, indent=2))