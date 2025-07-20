from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Geneva', 'Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Vilnius', 'Venice', 'Munich', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 27

    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Munich', 'Vienna'),
        ('Istanbul', 'Brussels'),
        ('Vienna', 'Vilnius'),
        ('Madrid', 'Munich'),
        ('Venice', 'Brussels'),
        ('Riga', 'Brussels'),
        ('Geneva', 'Istanbul'),
        ('Munich', 'Reykjavik'),
        ('Vienna', 'Istanbul'),
        ('Riga', 'Istanbul'),
        ('Reykjavik', 'Vienna'),
        ('Venice', 'Munich'),
        ('Madrid', 'Venice'),
        ('Vilnius', 'Istanbul'),
        ('Venice', 'Vienna'),
        ('Venice', 'Istanbul'),
        ('Reykjavik', 'Madrid'),
        ('Riga', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Reykjavik', 'Brussels'),
        ('Vilnius', 'Brussels'),
        ('Vilnius', 'Munich'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Geneva', 'Vienna'),
        ('Madrid', 'Brussels'),
        ('Vienna', 'Brussels'),
        ('Geneva', 'Brussels'),
        ('Geneva', 'Madrid'),
        ('Munich', 'Brussels'),
        ('Madrid', 'Istanbul'),
        ('Geneva', 'Munich'),
        ('Riga', 'Vilnius')
    ]

    # Create a set of possible transitions (bidirectional)
    transitions = set()
    for from_city, to_city in direct_flights:
        transitions.add((city_map[from_city], city_map[to_city]))
        transitions.add((city_map[to_city], city_map[from_city]))

    # Z3 variables: day[i] is the city on day i (1-based)
    day = [Int(f"day_{i}") for i in range(1, n_days + 1)]
    solver = Solver()

    # Each day's city must be valid
    for d in day:
        solver.add(And(d >= 0, d < n_cities))

    # Transition constraints: consecutive days must be either same city or connected by a direct flight
    for i in range(n_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        solver.add(Or(
            current_city == next_city,
            Or([And(current_city == from_idx, next_city == to_idx) for from_idx, to_idx in transitions])
        ))

    # Duration constraints
    # Istanbul: 4 days
    istanbul = city_map['Istanbul']
    solver.add(Sum([If(day[i] == istanbul, 1, 0) for i in range(n_days)]) == 4)

    # Vienna: 4 days
    vienna = city_map['Vienna']
    solver.add(Sum([If(day[i] == vienna, 1, 0) for i in range(n_days)]) == 4)

    # Riga: 2 days
    riga = city_map['Riga']
    solver.add(Sum([If(day[i] == riga, 1, 0) for i in range(n_days)]) == 2)

    # Brussels: 2 days, including day 26-27
    brussels = city_map['Brussels']
    solver.add(Sum([If(day[i] == brussels, 1, 0) for i in range(n_days)]) == 2)
    solver.add(day[25] == brussels)  # day 26 is index 25 (0-based)
    solver.add(day[26] == brussels)  # day 27 is index 26

    # Madrid: 4 days
    madrid = city_map['Madrid']
    solver.add(Sum([If(day[i] == madrid, 1, 0) for i in range(n_days)]) == 4)

    # Vilnius: 4 days, between day 20-23 (indices 19-22)
    vilnius = city_map['Vilnius']
    solver.add(Sum([If(day[i] == vilnius, 1, 0) for i in range(n_days)]) == 4)
    solver.add(Or(
        day[19] == vilnius,  # day 20
        day[20] == vilnius,
        day[21] == vilnius,
        day[22] == vilnius
    ))

    # Venice: 5 days, workshop between day 7-11 (indices 6-10)
    venice = city_map['Venice']
    solver.add(Sum([If(day[i] == venice, 1, 0) for i in range(n_days)]) == 5)
    solver.add(Or(
        day[6] == venice,  # day 7
        day[7] == venice,
        day[8] == venice,
        day[9] == venice,
        day[10] == venice
    ))

    # Geneva: 4 days, relatives between day 1-4 (indices 0-3)
    geneva = city_map['Geneva']
    solver.add(Sum([If(day[i] == geneva, 1, 0) for i in range(n_days)]) == 4)
    solver.add(Or(
        day[0] == geneva,
        day[1] == geneva,
        day[2] == geneva,
        day[3] == geneva
    ))

    # Munich: 5 days
    munich = city_map['Munich']
    solver.add(Sum([If(day[i] == munich, 1, 0) for i in range(n_days)]) == 5)

    # Reykjavik: 2 days
    reykjavik = city_map['Reykjavik']
    solver.add(Sum([If(day[i] == reykjavik, 1, 0) for i in range(n_days)]) == 2)

    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            city_idx = model.evaluate(day[i]).as_long()
            itinerary.append({"day": i + 1, "city": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))