from z3 import *
import json

def solve_itinerary():
    # Cities with correct spelling
    cities = ['Frankfurt', 'Naples', 'Helsinki', 'Lyon', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 12

    # Corrected direct flight connections
    adjacency = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }

    # Create Z3 variables for each day's city
    day_to_city = [Int(f'day_{i+1}_city') for i in range(n_days)]
    solver = Solver()

    # Each day must be assigned a valid city
    for day in day_to_city:
        solver.add(day >= 0, day < len(cities))

    # Flight transition constraints
    for i in range(n_days - 1):
        current = day_to_city[i]
        next_ = day_to_city[i + 1]
        # Either stay in same city or move to connected city
        solver.add(Or(
            current == next_,
            *[And(current == city_map[city], next_ == city_map[neighbor])
              for city in cities
              for neighbor in adjacency[city]]
        ))

    # Required days in each city
    required_days = {
        'Frankfurt': 3,
        'Naples': 4,
        'Helsinki': 4,
        'Lyon': 3,
        'Prague': 2
    }
    for city, days in required_days.items():
        solver.add(Sum([If(day_to_city[i] == city_map[city], 1, 0) 
                     for i in range(n_days)]) == days)

    # Helsinki must be days 2-5 (1-based)
    for i in [1, 2, 3, 4]:  # days 2-5 (0-based indices 1-4)
        solver.add(day_to_city[i] == city_map['Helsinki'])

    # Prague workshop on day 1 or 2
    solver.add(Or(
        day_to_city[0] == city_map['Prague'],
        day_to_city[1] == city_map['Prague']
    ))

    # Solve and return itinerary
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            city_idx = model.evaluate(day_to_city[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))