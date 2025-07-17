from z3 import *

def solve_itinerary():
    # Define the cities
    Madrid, Dublin, Tallinn = Ints('Madrid Dublin Tallinn')
    cities = {'Madrid': Madrid, 'Dublin': Dublin, 'Tallinn': Tallinn}
    
    # Days are 1..7
    days = 7
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Assign each city a unique integer
    city_ids = {'Madrid': 0, 'Dublin': 1, 'Tallinn': 2}
    city_names = {0: 'Madrid', 1: 'Dublin', 2: 'Tallinn'}
    
    # Constraints for each day's city
    for day in day_city:
        s.add(Or(day == 0, day == 1, day == 2))
    
    # Direct flights: transitions only between connected cities
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        # Possible transitions:
        # Madrid <-> Dublin (0 <-> 1)
        # Dublin <-> Tallinn (1 <-> 2)
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == 0, next_day == 1),  # Madrid to Dublin
            And(current == 1, next_day == 0),  # Dublin to Madrid
            And(current == 1, next_day == 2),  # Dublin to Tallinn
            And(current == 2, next_day == 1)   # Tallinn to Dublin
        ))
    
    # Total days per city
    madrid_days = Sum([If(day_city[i] == 0, 1, 0) for i in range(days)])
    dublin_days = Sum([If(day_city[i] == 1, 1, 0) for i in range(days)])
    tallinn_days = Sum([If(day_city[i] == 2, 1, 0) for i in range(days)])
    
    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)
    
    # Workshop constraint: Tallinn must be on day 6 or 7 (indices 5 or 6)
    s.add(Or(day_city[5] == 2, day_city[6] == 2))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_id = m.evaluate(day_city[i]).as_long()
            city_name = city_names[city_id]
            itinerary.append({'day': i + 1, 'place': city_name})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(result)