from z3 import *

def solve_itinerary():
    # Cities mapping
    cities = {
        'Manchester': 0,
        'Istanbul': 1,
        'Venice': 2,
        'Krakow': 3,
        'Lyon': 4
    }
    num_cities = len(cities)
    num_days = 21

    # Direct flights: adjacency list
    adjacency = {
        cities['Manchester']: [cities['Venice'], cities['Istanbul'], cities['Krakow']],
        cities['Istanbul']: [cities['Manchester'], cities['Venice'], cities['Krakow'], cities['Lyon']],
        cities['Venice']: [cities['Manchester'], cities['Istanbul'], cities['Lyon']],
        cities['Krakow']: [cities['Istanbul'], cities['Manchester']],
        cities['Lyon']: [cities['Venice'], cities['Istanbul']]
    }

    # Create Z3 variables: day i is spent in city s[i]
    s = [Int(f's_{i}') for i in range(num_days)]
    solver = Solver()

    # Each day must be one of the cities
    for i in range(num_days):
        solver.add(And(s[i] >= 0, s[i] < num_cities))

    # Flight transitions: consecutive days can only stay or move to adjacent cities
    for i in range(num_days - 1):
        current_city = s[i]
        next_city = s[i+1]
        possible_transitions = adjacency[current_city] + [current_city]  # Include staying in same city
        solver.add(Or([next_city == city for city in possible_transitions]))

    # Total days per city constraints
    manchester_days = Sum([If(s[i] == cities['Manchester'], 1, 0) for i in range(num_days)])
    istanbul_days = Sum([If(s[i] == cities['Istanbul'], 1, 0) for i in range(num_days)])
    venice_days = Sum([If(s[i] == cities['Venice'], 1, 0) for i in range(num_days)])
    krakow_days = Sum([If(s[i] == cities['Krakow'], 1, 0) for i in range(num_days)])
    lyon_days = Sum([If(s[i] == cities['Lyon'], 1, 0) for i in range(num_days)])

    solver.add(manchester_days == 3)
    solver.add(istanbul_days == 7)
    solver.add(venice_days == 7)
    solver.add(krakow_days == 6)
    solver.add(lyon_days == 2)

    # Manchester must be visited between day 1-3 (days 0, 1, 2 in zero-based)
    solver.add(Or([s[i] == cities['Manchester'] for i in range(3)]))

    # Workshop in Venice between day 3 and 9 (days 2 to 8 in zero-based)
    solver.add(Or([s[i] == cities['Venice'] for i in range(2, 9)]))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = {v: k for k, v in cities.items()}
        for i in range(num_days):
            city_num = model.evaluate(s[i]).as_long()
            itinerary.append({'day': i + 1, 'city': city_names[city_num]})
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))