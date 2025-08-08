from z3 import *

def solve_itinerary():
    s = Solver()

    days = 15
    city_codes = {'S': 0, 'V': 1, 'M': 2}  # S: Stuttgart, V: Seville, M: Manchester

    # Create variables for each day's city
    day_city = [Int(f"day_{day}_city") for day in range(1, days + 1)]

    # Each day's city must be 0 (S), 1 (V), or 2 (M)
    for day in day_city:
        s.add(Or(day == city_codes['S'], day == city_codes['V'], day == city_codes['M']))

    # Constraints for total days in each city
    total_S = Int('total_S')
    total_V = Int('total_V')
    total_M = Int('total_M')

    s.add(total_S == Sum([If(day == city_codes['S'], 1, 0) for day in day_city]))
    s.add(total_V == Sum([If(day == city_codes['V'], 1, 0) for day in day_city]))
    s.add(total_M == Sum([If(day == city_codes['M'], 1, 0) for day in day_city]))

    s.add(total_S == 6)
    s.add(total_V == 7)
    s.add(total_M == 4)

    # Constraint: Meet friend in Stuttgart between day 1 and day 6 (i.e., at least one day S in days 1-6)
    s.add(Or([day_city[i] == city_codes['S'] for i in range(6)]))

    # Flight constraints: transitions must be via direct flights
    # Direct flights: M<->V, S<->M
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == city_codes['S'], next_day == city_codes['M']),
            And(current == city_codes['M'], next_day == city_codes['S']),
            And(current == city_codes['M'], next_day == city_codes['V']),
            And(current == city_codes['V'], next_day == city_codes['M'])
        ))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, days + 1):
            city_var = day_city[day - 1]
            city_val = model[city_var].as_long()
            if city_val == city_codes['S']:
                itinerary.append({"day": day, "place": "Stuttgart"})
            elif city_val == city_codes['V']:
                itinerary.append({"day": day, "place": "Seville"})
            elif city_val == city_codes['M']:
                itinerary.append({"day": day, "place": "Manchester"})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))