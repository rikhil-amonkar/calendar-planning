from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {
        'Nice': 0,
        'Stockholm': 1,
        'Split': 2,
        'Vienna': 3
    }
    num_cities = len(cities)
    num_days = 9

    # Direct flights: adjacency list
    direct_flights = {
        cities['Vienna']: [cities['Stockholm'], cities['Nice'], cities['Split']],
        cities['Stockholm']: [cities['Vienna'], cities['Split'], cities['Nice']],
        cities['Nice']: [cities['Vienna'], cities['Stockholm']],
        cities['Split']: [cities['Vienna'], cities['Stockholm']]
    }

    # Create Z3 variables: each day is assigned a city
    day_to_city = [Int(f'day_{i}_city') for i in range(1, num_days + 1)]

    s = Solver()

    # Each day's city must be one of the four cities
    for day in range(num_days):
        s.add(And(day_to_city[day] >= 0, day_to_city[day] < num_cities))

    # Constraints for transitions: consecutive days must be same city or connected by direct flight
    for i in range(num_days - 1):
        current_city = day_to_city[i]
        next_city = day_to_city[i + 1]
        # Either stay in the same city or move to a city with a direct flight
        s.add(Or(
            current_city == next_city,
            *[next_city == city for city in direct_flights[current_city]]
        ))

    # Days in each city constraints
    # Nice: 2 days
    nice_days = Sum([If(day_to_city[i] == cities['Nice'], 1, 0) for i in range(num_days)])
    s.add(nice_days == 2)

    # Stockholm: 5 days
    stockholm_days = Sum([If(day_to_city[i] == cities['Stockholm'], 1, 0) for i in range(num_days)])
    s.add(stockholm_days == 5)

    # Split: 3 days, including days 7 and 9 (1-based)
    split_days = Sum([If(day_to_city[i] == cities['Split'], 1, 0) for i in range(num_days)])
    s.add(split_days == 3)
    s.add(day_to_city[6] == cities['Split'])  # Day 7 is index 6 (0-based)
    s.add(day_to_city[8] == cities['Split'])  # Day 9 is index 8

    # Vienna: 2 days, and workshop between day 1 and 2 (so must be in Vienna on day 1 or 2)
    vienna_days = Sum([If(day_to_city[i] == cities['Vienna'], 1, 0) for i in range(num_days)])
    s.add(vienna_days == 2)
    s.add(Or(day_to_city[0] == cities['Vienna'], day_to_city[1] == cities['Vienna']))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for day in range(num_days):
            city_code = m.evaluate(day_to_city[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'city': city_names[city_code]
            })
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))