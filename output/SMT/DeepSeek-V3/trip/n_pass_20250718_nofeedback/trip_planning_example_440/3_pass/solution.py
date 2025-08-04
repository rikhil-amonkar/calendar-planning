from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    num_cities = len(cities)
    num_days = 12

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4],  # Split: Helsinki, Vilnius, Geneva
        1: [0, 2, 3, 4],  # Helsinki: Split, Reykjavik, Vilnius, Geneva
        2: [1],          # Reykjavik: Helsinki
        3: [0, 1],       # Vilnius: Split, Helsinki
        4: [0, 1]        # Geneva: Split, Helsinki
    }

    # Create Z3 variables: day[i] is the city visited on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(num_days)]

    s = Solver()

    # Each day must be a valid city (0 to 4)
    for d in day:
        s.add(And(d >= 0, d < num_cities))

    # Transition constraints: consecutive days must be the same city or connected by a direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            Or([next_city == j for j in direct_flights[current_city.as_long()]])
        ))

    # Count days per city
    counts = [Int(f'count_{city}') for city in range(num_cities)]
    for city in range(num_cities):
        s.add(counts[city] == Sum([If(day[i] == city, 1, 0) for i in range(num_days)]))

    # Days per city constraints
    s.add(counts[cities['Split']] == 2)
    s.add(counts[cities['Helsinki']] == 2)
    s.add(counts[cities['Reykjavik']] == 3)
    s.add(counts[cities['Vilnius']] == 3)
    s.add(counts[cities['Geneva']] == 6)

    # Reykjavik between day 10 and 12 (1-based, so indices 9-11 in 0-based)
    s.add(Or([day[i] == cities['Reykjavik'] for i in [9, 10, 11]]))

    # Vilnius between day 7 and 9 (indices 6-8 in 0-based)
    s.add(Or([day[i] == cities['Vilnius'] for i in [6, 7, 8]]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for i in range(num_days):
            city_code = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i + 1, 'place': city_names[city_code]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))