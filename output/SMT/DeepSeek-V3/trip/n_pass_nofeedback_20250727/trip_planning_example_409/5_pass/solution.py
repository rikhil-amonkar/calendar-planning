from z3 import *

def solve_itinerary():
    # Cities mapping
    cities = {
        'Zurich': 0,
        'Hamburg': 1,
        'Helsinki': 2,
        'Bucharest': 3,
        'Split': 4
    }
    num_cities = len(cities)
    num_days = 12

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3, 4],  # Zurich
        1: [0, 2, 3, 4],   # Hamburg
        2: [0, 1, 4],      # Helsinki
        3: [0, 1],         # Bucharest
        4: [0, 1, 2]       # Split
    }

    # Create Z3 variables: day[i] is the city on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(num_days)]

    s = Solver()

    # Each day's city must be one of the 5 cities
    for d in day:
        s.add(Or([d == c for c in cities.values()]))

    # Transition constraints: consecutive days must be same city or have a direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Create a list of possible transitions
        transitions = [current_city == next_city]
        for city in cities.values():
            if city in direct_flights:
                for adj in direct_flights[city]:
                    transitions.append(And(current_city == city, next_city == adj))
        s.add(Or(transitions))

    # Days in each city constraints
    # Zurich: 3 days (including any flight days)
    s.add(Sum([If(day[d] == cities['Zurich'], 1, 0) for d in range(num_days)]) == 3)
    # Wedding in Zurich between day 1 and day 3 (so Zurich must be on at least one of days 0, 1, or 2 (0-based) (days 1, 2, or 3 1-based)
    s.add(Or([day[d] == cities['Zurich'] for d in range(3)]))

    # Hamburg: 2 days
    s.add(Sum([If(day[d] == cities['Hamburg'], 1, 0) for d in range(num_days)]) == 2)

    # Helsinki: 2 days
    s.add(Sum([If(day[d] == cities['Helsinki'], 1, 0) for d in range(num_days)]) == 2)

    # Bucharest: 2 days
    s.add(Sum([If(day[d] == cities['Bucharest'], 1, 0) for d in range(num_days)]) == 2)

    # Split: 7 days, must include day 3 (0-based day 3 is day 4) and day 9 (0-based day 9 is day 10)
    s.add(Sum([If(day[d] == cities['Split'], 1, 0) for d in range(num_days)]) == 7)
    s.add(day[3] == cities['Split'])  # day 4 (1-based)
    s.add(day[9] == cities['Split'])  # day 10 (1-based)

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for d in range(num_days):
            city_code = m.evaluate(day[d]).as_long()
            itinerary.append({'day': d + 1, 'place': city_names[city_code]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))