from z3 import *

def solve_itinerary():
    s = Solver()
    
    # Days are 1 to 7
    days = range(1, 8)
    
    # Cities mapping
    cities = {'Riga': 0, 'Amsterdam': 1, 'Mykonos': 2}
    reverse_map = {0: 'Riga', 1: 'Amsterdam', 2: 'Mykonos'}
    
    # Variables: city for each day
    city_day = [Int(f'city_{d}') for d in days]
    
    # Flight variables: is there a flight on this day?
    flight_day = [Bool(f'flight_{d}') for d in days]
    
    # City constraints (0-2)
    for d in days:
        s.add(And(city_day[d-1] >= 0, city_day[d-1] <= 2))
    
    # Flight constraints
    for d in days:
        # If flight day, next day must be connected
        if d < 7:
            s.add(Implies(flight_day[d-1],
                         Or(And(city_day[d-1] == cities['Amsterdam'], city_day[d] == cities['Mykonos']),
                            And(city_day[d-1] == cities['Mykonos'], city_day[d] == cities['Amsterdam']),
                            And(city_day[d-1] == cities['Riga'], city_day[d] == cities['Amsterdam']),
                            And(city_day[d-1] == cities['Amsterdam'], city_day[d] == cities['Riga']))))
        
        # Flight day counts for both cities
        if d < 7:
            s.add(Implies(flight_day[d-1],
                         Not(city_day[d-1] == city_day[d])))
    
    # Initial conditions (days 1-2 in Riga)
    s.add(city_day[0] == cities['Riga'])
    s.add(city_day[1] == cities['Riga'])
    s.add(Not(flight_day[0]))  # No flight on day 1
    s.add(Not(flight_day[1]))  # No flight on day 2
    
    # Count days in each city
    def count_days(city_var):
        total = 0
        for d in days:
            # Current day counts
            total += If(city_day[d-1] == city_var, 1, 0)
            # If flight day, next city also counts
            if d < 7:
                total += If(And(flight_day[d-1], city_day[d] == city_var), 1, 0)
        return total
    
    s.add(count_days(cities['Riga']) == 2)
    s.add(count_days(cities['Amsterdam']) == 2)
    s.add(count_days(cities['Mykonos']) == 5)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in days:
            current_city = m.evaluate(city_day[d-1]).as_long()
            place = reverse_map[current_city]
            if d < 7 and m.evaluate(flight_day[d-1]):
                next_city = m.evaluate(city_day[d]).as_long()
                place += f"/{reverse_map[next_city]}"
            itinerary.append({'day': d, 'place': place})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))