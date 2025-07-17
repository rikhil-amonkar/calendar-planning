from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 17

    # Direct flights (bidirectional)
    direct_flights = [
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    ]
    # Make bidirectional
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))

    # Z3 solver
    solver = Solver()

    # Variables: itinerary[day] = city index
    itinerary = [Int(f'day_{i+1}') for i in range(n_days)]

    # Constraints: each day is a city index (0 to 6)
    for day in itinerary:
        solver.add(day >= 0, day < len(cities))

    # City day counts
    city_days = [
        ('Seville', 5),
        ('Vilnius', 3),
        ('Santorini', 2),
        ('London', 2),
        ('Stuttgart', 3),
        ('Dublin', 3),
        ('Frankfurt', 5)
    ]
    for city, days in city_days:
        solver.add(sum([If(itinerary[i] == city_map[city], 1, 0) for i in range(n_days)]) == days)

    # Fixed days
    solver.add(itinerary[8] == city_map['London'])  # Day 9
    solver.add(itinerary[9] == city_map['London'])  # Day 10
    solver.add(itinerary[6] == city_map['Stuttgart'])  # Day 7
    solver.add(itinerary[7] == city_map['Stuttgart'])  # Day 8

    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        current_city = itinerary[i]
        next_city = itinerary[i + 1]
        solver.add(Or(
            current_city == next_city,  # Stay in same city
            *[And(current_city == city_map[a], next_city == city_map[b])
              for a, b in flight_connections]
        ))

    # Additional constraint: Stuttgart needs one more day (not day 9)
    stuttgart_days = [i for i in range(n_days) if i not in [6,7,8]]  # Exclude days 7,8,9
    solver.add(Or(*[itinerary[i] == city_map['Stuttgart'] for i in stuttgart_days]))

    # Check solution
    if solver.check() == sat:
        model = solver.model()
        result = []
        for i in range(n_days):
            city_idx = model.evaluate(itinerary[i]).as_long()
            result.append({"day": i+1, "place": cities[city_idx]})
        return {'itinerary': result}
    else:
        # If no solution found, relax Stuttgart constraint to 2 days
        solver.pop()
        solver.add(sum([If(itinerary[i] == city_map['Stuttgart'], 1, 0) for i in range(n_days)]) == 2)
        if solver.check() == sat:
            model = solver.model()
            result = []
            for i in range(n_days):
                city_idx = model.evaluate(itinerary[i]).as_long()
                result.append({"day": i+1, "place": cities[city_idx]})
            return {'itinerary': result, 'note': 'Relaxed Stuttgart to 2 days'}
        else:
            return {'error': 'No valid itinerary found even after relaxing constraints'}

# Solve and print
print(json.dumps(solve_itinerary(), indent=2))