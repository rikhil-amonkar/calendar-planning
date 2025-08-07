from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Krakow': 0,
        'Frankfurt': 1,
        'Oslo': 2,
        'Dubrovnik': 3,
        'Naples': 4
    }
    num_cities = len(cities)
    num_days = 18

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2],  # Krakow: Frankfurt, Oslo
        1: [0, 2, 3],  # Frankfurt: Krakow, Oslo, Dubrovnik
        2: [0, 1, 3, 4],  # Oslo: Krakow, Frankfurt, Dubrovnik, Naples
        3: [1, 2, 4],  # Dubrovnik: Frankfurt, Oslo, Naples
        4: [2, 3, 1]   # Naples: Oslo, Dubrovnik, Frankfurt
    }

    # Create Z3 variables: itinerary[d] is the city on day d (1-based)
    itinerary = [Int(f'day_{d}') for d in range(1, num_days + 1)]

    # Solver
    s = Solver()

    # Each day's city must be a valid city (0 to 4)
    for day in itinerary:
        s.add(day >= 0, day < num_cities)

    # Constraint: transitions between cities must be direct flights
    for d in range(num_days - 1):
        current_city = itinerary[d]
        next_city = itinerary[d + 1]
        # Ensure next_city is in direct_flights of current_city or same city
        s.add(Or([next_city == city for city in direct_flights[current_city.as_long() if is_const(current_city) else current_city]] + [next_city == current_city]))

    # Total days constraints
    city_days = [0] * num_cities
    for city_idx in range(num_cities):
        city_days[city_idx] = Sum([If(itinerary[d] == city_idx, 1, 0) for d in range(num_days)])
    s.add(city_days[cities['Krakow']] == 5)
    s.add(city_days[cities['Frankfurt']] == 4)
    s.add(city_days[cities['Oslo']] == 3)
    s.add(city_days[cities['Dubrovnik']] == 5)
    s.add(city_days[cities['Naples']] == 5)

    # Oslo must be visited between day 16 and 18 (inclusive)
    oslo_days = [If(itinerary[d] == cities['Oslo'], 1, 0) for d in range(15, 18)]  # days 16-18 (0-based 15-17)
    s.add(Sum(oslo_days) >= 1)

    # Dubrovnik must be visited between day 5 and 9 (inclusive)
    dubrovnik_days = [If(itinerary[d] == cities['Dubrovnik'], 1, 0) for d in range(4, 9)]  # days 5-9 (0-based 4-8)
    s.add(Sum(dubrovnik_days) >= 1)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary_result = []
        city_names = {v: k for k, v in cities.items()}
        for d in range(num_days):
            city_code = model.evaluate(itinerary[d]).as_long()
            itinerary_result.append({'day': d + 1, 'place': city_names[city_code]})
        return {'itinerary': itinerary_result}
    else:
        return None

# Execute and print result
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")