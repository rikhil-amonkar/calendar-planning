from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {
        'Paris': 0,
        'Madrid': 1,
        'Bucharest': 2,
        'Seville': 3
    }
    inv_cities = {v: k for k, v in cities.items()}

    # Direct flights: adjacency list
    direct_flights = {
        cities['Paris']: [cities['Bucharest'], cities['Seville'], cities['Madrid']],
        cities['Madrid']: [cities['Paris'], cities['Bucharest'], cities['Seville']],
        cities['Bucharest']: [cities['Paris'], cities['Madrid']],
        cities['Seville']: [cities['Paris'], cities['Madrid']]
    }

    # Create Z3 variables for each day (1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]  # days 1 to 15

    s = Solver()

    # Constraint: each day must be one of the cities
    for day in days:
        s.add(Or([day == cities[c] for c in cities.keys()]))

    # Constraint: days 1-7 must be Madrid
    for i in range(0, 7):  # days 1-7 (indices 0-6 in list)
        s.add(days[i] == cities['Madrid'])

    # Constraint: days 14-15 must be Bucharest
    s.add(days[13] == cities['Bucharest'])  # day 14 (index 13)
    s.add(days[14] == cities['Bucharest'])  # day 15 (index 14)

    # Transition constraints: consecutive days must be same city or have a direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # Either same city or there's a direct flight
        s.add(Or(
            current_city == next_city,
            Or([next_city == adj for adj in direct_flights[current_city.as_long()]])
        ))

    # Total days constraints
    paris_days = Sum([If(d == cities['Paris'], 1, 0) for d in days])
    madrid_days = Sum([If(d == cities['Madrid'], 1, 0) for d in days])
    bucharest_days = Sum([If(d == cities['Bucharest'], 1, 0) for d in days])
    seville_days = Sum([If(d == cities['Seville'], 1, 0) for d in days])

    s.add(paris_days == 6)
    s.add(madrid_days == 7)
    s.add(bucharest_days == 2)
    s.add(seville_days == 3)

    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 16):
            day_var = days[i - 1]
            city_code = m.evaluate(day_var).as_long()
            city_name = inv_cities[city_code]
            itinerary.append({'day': i, 'place': city_name})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))