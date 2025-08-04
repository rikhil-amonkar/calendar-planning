from z3 import *

def solve_itinerary():
    s = Solver()

    # Days 1-9
    days = range(1, 10)
    n_days = len(days)

    # Cities: Mykonos (M), Budapest (B), Hamburg (H)
    cities = ['M', 'B', 'H']
    city_vars = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in days]

    # Constraints for each day
    for day_idx in range(n_days):
        # At least one city per day
        s.add(Or(city_vars[day_idx][0], city_vars[day_idx][1], city_vars[day_idx][2]))
        
        # No three cities on same day
        s.add(Not(And(city_vars[day_idx][0], city_vars[day_idx][1], city_vars[day_idx][2])))
        
        # If two cities, they must be connected
        for i in range(3):
            for j in range(i+1, 3):
                ci = cities[i]
                cj = cities[j]
                connected = (ci == 'B' and cj == 'M') or (ci == 'B' and cj == 'H') or \
                           (cj == 'B' and ci == 'M') or (cj == 'B' and ci == 'H')
                if not connected:
                    s.add(Not(And(city_vars[day_idx][i], city_vars[day_idx][j])))

    # Total days per city (counting travel days for both cities)
    total_M = sum([If(city_vars[day_idx][0], 1, 0) for day_idx in range(n_days)])
    total_B = sum([If(city_vars[day_idx][1], 1, 0) for day_idx in range(n_days)])
    total_H = sum([If(city_vars[day_idx][2], 1, 0) for day_idx in range(n_days)])

    s.add(total_M == 6)
    s.add(total_B == 3)
    s.add(total_H == 2)

    # Mandatory days in Mykonos (must be single-city days)
    s.add(city_vars[3][0] == True)  # day 4 is M only
    s.add(Not(Or(city_vars[3][1], city_vars[3][2])))
    s.add(city_vars[8][0] == True)  # day 9 is M only
    s.add(Not(Or(city_vars[8][1], city_vars[8][2])))

    # Transition constraints between days
    for day_idx in range(n_days - 1):
        current = city_vars[day_idx]
        next_day = city_vars[day_idx + 1]
        
        # From M: can stay or go to B
        s.add(Implies(current[0], Or(next_day[0], next_day[1])))
        # From B: can stay or go to M or H
        s.add(Implies(current[1], Or(next_day[1], next_day[0], next_day[2])))
        # From H: can stay or go to B
        s.add(Implies(current[2], Or(next_day[2], next_day[1])))

    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day_idx in range(n_days):
            day_num = day_idx + 1
            places = []
            for city_idx in range(3):
                if is_true(model[city_vars[day_idx][city_idx]]):
                    places.append(cities[city_idx])
            itinerary.append({"day": day_num, "place": places})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))