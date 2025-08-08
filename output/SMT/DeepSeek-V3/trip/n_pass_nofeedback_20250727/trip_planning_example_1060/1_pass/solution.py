from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 25
    n_cities = len(cities)

    # Direct flights: adjacency list
    direct_flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Vilnius', 'Valencia', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Stuttgart': ['Valencia', 'Istanbul', 'Reykjavik'],
        'Munich': ['Reykjavik', 'Geneva', 'Vilnius', 'Seville', 'Istanbul', 'Valencia'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Vilnius': ['Istanbul', 'Munich']
    }

    # Correcting city names in the flight list
    direct_flights['Munich'] = direct_flights['Munich'] if 'Munich' in direct_flights else direct_flights.get('Munich', [])
    direct_flights['Geneva'] = direct_flights['Geneva']  # assuming correct

    # Create a list of all possible flight transitions (a, b)
    flight_transitions = []
    for a in direct_flights:
        if a not in city_map:
            continue
        a_idx = city_map[a]
        for b in direct_flights[a]:
            if b not in city_map:
                continue
            b_idx = city_map[b]
            flight_transitions.append((a_idx, b_idx))

    # Z3 variables: for each day, which city is visited?
    X = [Int(f'day_{i}') for i in range(1, n_days + 1)]

    s = Solver()

    # Each day's city must be between 0 and n_cities-1
    for x in X:
        s.add(x >= 0)
        s.add(x < n_cities)

    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(n_days - 1):
        current_city = X[i]
        next_city = X[i + 1]
        # Option 1: stay in the same city
        same_city = (current_city == next_city)
        # Option 2: move to a directly connected city
        flight_options = []
        for a_idx, b_idx in flight_transitions:
            flight_options.append(And(current_city == a_idx, next_city == b_idx))
        s.add(Or(same_city, *flight_options))

    # Duration constraints
    # Stuttgart: 4 days total, includes day 4 and day 7
    stuttgart_days = [If(X[i] == city_map['Stuttgart'], 1, 0) for i in range(n_days)]
    s.add(Sum(stuttgart_days) == 4)
    s.add(Or(X[3] == city_map['Stuttgart']))  # day 4 is index 3
    s.add(Or(X[6] == city_map['Stuttgart']))  # day 7 is index 6

    # Istanbul: 4 days, between day 19-22 (indices 18-21)
    istanbul_days = [If(X[i] == city_map['Istanbul'], 1, 0) for i in range(n_days)]
    s.add(Sum(istanbul_days) == 4)
    # At least one day between 19-22 must be Istanbul
    s.add(Or([X[i] == city_map['Istanbul'] for i in range(18, 22)]))

    # Vilnius: 4 days
    vilnius_days = [If(X[i] == city_map['Vilnius'], 1, 0) for i in range(n_days)]
    s.add(Sum(vilnius_days) == 4)

    # Seville: 3 days
    seville_days = [If(X[i] == city_map['Seville'], 1, 0) for i in range(n_days)]
    s.add(Sum(seville_days) == 3)

    # Geneva: 5 days
    geneva_days = [If(X[i] == city_map['Geneva'], 1, 0) for i in range(n_days)]
    s.add(Sum(geneva_days) == 5)

    # Valencia: 5 days
    valencia_days = [If(X[i] == city_map['Valencia'], 1, 0) for i in range(n_days)]
    s.add(Sum(valencia_days) == 5)

    # Munich: 3 days, includes days 13-15 (indices 12-14)
    munich_days = [If(X[i] == city_map['Munich'], 1, 0) for i in range(n_days)]
    s.add(Sum(munich_days) == 3)
    s.add(Or(X[12] == city_map['Munich']))  # day 13
    s.add(Or(X[13] == city_map['Munich']))  # day 14
    s.add(Or(X[14] == city_map['Munich']))  # day 15

    # Reykjavik: 4 days, includes days 1-4 (indices 0-3)
    reykjavik_days = [If(X[i] == city_map['Reykjavik'], 1, 0) for i in range(n_days)]
    s.add(Sum(reykjavik_days) == 4)
    s.add(Or(X[0] == city_map['Reykjavik']))  # day 1
    s.add(Or(X[1] == city_map['Reykjavik']))  # day 2
    s.add(Or(X[2] == city_map['Reykjavik']))  # day 3
    s.add(Or(X[3] == city_map['Reykjavik']))  # day 4

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = m.evaluate(X[i]).as_long()
            itinerary.append({'day': i + 1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)