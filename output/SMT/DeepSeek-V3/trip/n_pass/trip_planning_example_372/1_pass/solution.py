from z3 import *
import json

def solve_itinerary():
    # Cities encoding
    cities = {'Seville': 0, 'Stuttgart': 1, 'Porto': 2, 'Madrid': 3}
    city_names = {0: 'Seville', 1: 'Stuttgart', 2: 'Porto', 3: 'Madrid'}

    # Direct flight connections (undirected)
    connections = {
        0: [2, 3],  # Seville connected to Porto and Madrid
        1: [2],      # Stuttgart connected to Porto
        2: [0, 1, 3],# Porto connected to Seville, Stuttgart, Madrid
        3: [0, 2]    # Madrid connected to Seville, Porto
    }

    # Create Z3 variables: day[i] represents the city on day i+1 (1-based)
    days = [Int(f'day_{i}') for i in range(13)]

    s = Solver()

    # Each day must be one of the four cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))

    # Transition constraints: consecutive days must be the same or connected
    allowed_transitions = []
    for c1 in cities.values():
        allowed_transitions.append((c1, c1))  # staying is allowed
        for c2 in connections.get(c1, []):
            allowed_transitions.append((c1, c2))
    # Now, for each i, (days[i], days[i+1]) must be in allowed_transitions.
    for i in range(12):
        s.add(Or([And(days[i] == t[0], days[i+1] == t[1]) for t in allowed_transitions]))

    # Constraints:
    # Seville total days: 2
    s.add(Sum([If(days[i] == 0, 1, 0) for i in range(13)]) == 2)

    # Stuttgart total days: 7, including day7 (index 6) and day13 (index 12)
    s.add(days[6] == 1)  # day7
    s.add(days[12] == 1) # day13
    s.add(Sum([If(days[i] == 1, 1, 0) for i in range(13)]) == 7)

    # Porto total days: 3
    s.add(Sum([If(days[i] == 2, 1, 0) for i in range(13)]) == 3)

    # Madrid total days: 4, and at least one day between day1-day4 (indices 0-3)
    s.add(Sum([If(days[i] == 3, 1, 0) for i in range(13)]) == 4)
    s.add(Or([days[i] == 3 for i in range(4)]))

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(13):
            day = i + 1
            city_code = model.evaluate(days[i]).as_long()
            city = city_names[city_code]
            itinerary.append({'day': day, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))