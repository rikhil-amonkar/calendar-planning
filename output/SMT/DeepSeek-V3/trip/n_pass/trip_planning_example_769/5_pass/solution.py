from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Porto': 0,
        'Prague': 1,
        'Reykjavik': 2,
        'Santorini': 3,
        'Amsterdam': 4,
        'Munich': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [4, 5],  # Porto: Amsterdam, Munich
        1: [2, 4, 5],  # Prague: Reykjavik, Amsterdam, Munich
        2: [1, 4, 5],  # Reykjavik: Prague, Amsterdam, Munich
        3: [4],  # Santorini: Amsterdam
        4: [0, 1, 2, 3, 5],  # Amsterdam: Porto, Prague, Reykjavik, Santorini, Munich
        5: [0, 1, 2, 4]  # Munich: Porto, Prague, Reykjavik, Amsterdam
    }
    
    # Days: 1 to 16 (1-based)
    num_days = 16
    days = range(1, num_days + 1)
    
    # Create Z3 variables
    s = Solver()
    day_city = [Int(f'day_{day}_city') for day in days]
    
    # Each day's city must be valid (0-5)
    for dc in day_city:
        s.add(And(dc >= 0, dc <= 5))
    
    # Flight constraints
    for i in range(num_days - 1):
        current = day_city[i]
        next_c = day_city[i+1]
        # Either stay in same city or fly to connected city
        s.add(Or(
            current == next_c,
            *[And(current == src, next_c == dst) 
              for src in direct_flights for dst in direct_flights[src]]
        ))
    
    # Total days per city (including flight days)
    for city, code in cities.items():
        total_days = Sum([If(day_city[i] == code, 1, 0) for i in range(num_days)])
        if city == 'Porto':
            s.add(total_days == 5)
        elif city == 'Prague':
            s.add(total_days == 4)
        elif city == 'Reykjavik':
            s.add(total_days == 4)
        elif city == 'Santorini':
            s.add(total_days == 2)
        elif city == 'Amsterdam':
            s.add(total_days == 2)
        elif city == 'Munich':
            s.add(total_days == 4)
    
    # Event constraints:
    # Wedding in Reykjavik between day 4 and day 7 (inclusive)
    s.add(Or([day_city[i] == cities['Reykjavik'] for i in range(3, 7)]))
    
    # Conference in Amsterdam on day 14 and 15
    s.add(day_city[13] == cities['Amsterdam'])
    s.add(day_city[14] == cities['Amsterdam'])
    
    # Meet friend in Munich between day 7 and day 10
    s.add(Or([day_city[i] == cities['Munich'] for i in range(6, 10)]))
    
    # Additional constraints to help the solver:
    # No consecutive flights (prevent rapid bouncing)
    for i in range(num_days - 2):
        s.add(Not(And(day_city[i] != day_city[i+1], day_city[i+1] != day_city[i+2])))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(num_days):
            city_code = model.evaluate(day_city[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'city': city_names[city_code]
            })
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))