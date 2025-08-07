from z3 import *

def solve_itinerary():
    # Cities
    Split, Helsinki, Reykjavik, Vilnius, Geneva = Ints('Split Helsinki Reykjavik Vilnius Geneva')
    cities = {
        'Split': Split,
        'Helsinki': Helsinki,
        'Reykjavik': Reykjavik,
        'Vilnius': Vilnius,
        'Geneva': Geneva
    }
    city_ids = {name: idx for idx, name in enumerate(cities.keys())}
    n_cities = len(cities)
    n_days = 12

    # Direct flights: adjacency list
    direct_flights = {
        'Split': ['Helsinki', 'Geneva', 'Vilnius'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Reykjavik': ['Helsinki'],
        'Vilnius': ['Helsinki', 'Split'],
        'Geneva': ['Split', 'Helsinki']
    }

    # Create a Z3 solver
    s = Solver()

    # Variables: day[i] is the city visited on day i+1 (days 1..12)
    day = [Int(f'day_{i}') for i in range(n_days)]

    # Each day must be one of the cities (0 to 4)
    for d in day:
        s.add(And(d >= 0, d < n_cities))

    # Constraints for days in each city
    # Total days per city:
    # Split: 2, Helsinki: 2, Reykjavik:3 (days 10-12), Vilnius:3 (days7-9), Geneva:6
    # Count occurrences of each city in the day array
    counts = [Int(f'count_{city}') for city in cities]
    for idx, city in enumerate(cities.keys()):
        s.add(counts[idx] == Sum([If(day[i] == idx, 1, 0) for i in range(n_days)]))

    s.add(counts[city_ids['Split']] == 2)
    s.add(counts[city_ids['Helsinki']] == 2)
    s.add(counts[city_ids['Reykjavik']] == 3)
    s.add(counts[city_ids['Vilnius']] == 3)
    s.add(counts[city_ids['Geneva']] == 6)

    # Reykjavik must be on days 10,11,12 (indices 9,10,11)
    for i in [9, 10, 11]:
        s.add(day[i] == city_ids['Reykjavik'])

    # Vilnius must be on days 7,8,9 (indices 6,7,8)
    for i in [6, 7, 8]:
        s.add(day[i] == city_ids['Vilnius'])

    # Flight transitions: consecutive days must be the same city or connected by direct flight
    for i in range(n_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # Either same city or connected
        same_city = current_city == next_city
        # Possible connections
        connections = []
        for city in cities.keys():
            for neighbor in direct_flights.get(city, []):
                c1 = city_ids[city]
                c2 = city_ids[neighbor]
                connections.append(And(current_city == c1, next_city == c2))
                connections.append(And(current_city == c2, next_city == c1))
        s.add(Or(same_city, *connections))

    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = list(cities.keys())
        for i in range(n_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i+1, 'city': city_names[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the solution
solution = solve_itinerary()
print(solution)