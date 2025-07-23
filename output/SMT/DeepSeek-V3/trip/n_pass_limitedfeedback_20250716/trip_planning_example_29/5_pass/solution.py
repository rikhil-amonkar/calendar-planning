from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities mapping
    cities = ['Dubrovnik', 'Frankfurt', 'Krakow']
    D, F, K = 0, 1, 2

    # Days 1-10
    days = 10
    day_vars = [Int(f'day_{i}') for i in range(1, days+1)]

    # Each day must be one of the cities
    for day in day_vars:
        s.add(Or(day == D, day == F, day == K))

    # Wedding in Krakow on days 9-10
    s.add(day_vars[8] == K)  # day 9
    s.add(day_vars[9] == K)  # day 10

    # Count days in each city
    d_days = Sum([If(day == D, 1, 0) for day in day_vars])
    f_days = Sum([If(day == F, 1, 0) for day in day_vars])
    k_days = Sum([If(day == K, 1, 0) for day in day_vars])

    s.add(d_days == 7)
    s.add(f_days == 3)
    s.add(k_days == 2)

    # Flight constraints
    for i in range(days-1):
        current = day_vars[i]
        next_day = day_vars[i+1]
        s.add(Or(
            current == next_day,  # stay in same city
            And(current == F, next_day == K),  # F->K
            And(current == K, next_day == F),  # K->F
            And(current == D, next_day == F),  # D->F
            And(current == F, next_day == D)   # F->D
        ))

    # Additional constraints to help solver
    # Must start in either Dubrovnik or Frankfurt (can't start in Krakow)
    s.add(Or(day_vars[0] == D, day_vars[0] == F))
    
    # Must have at least one transition to Krakow before day 9
    # (since we can't be in Krakow before day 9 except for travel)
    s.add(Or([day_vars[i] == K for i in range(8)]))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_code = m.evaluate(day_vars[i]).as_long()
            city_name = cities[city_code]
            itinerary.append({'day': day_num, 'place': city_name})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

print(solve_itinerary())