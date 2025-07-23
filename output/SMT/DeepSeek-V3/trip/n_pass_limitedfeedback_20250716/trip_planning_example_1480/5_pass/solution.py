from z3 import *

def solve_itinerary():
    # Cities with correct spelling
    cities = ['Geneva', 'Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Vilnius', 'Venice', 'Munich', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 27

    # Corrected direct flights list
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

    # Create bidirectional transitions
    transitions = set()
    for from_city, to_city in direct_flights:
        transitions.add((city_map[from_city], city_map[to_city]))
        transitions.add((city_map[to_city], city_map[from_city]))

    # Z3 variables for each day
    day = [Int(f"day_{i}") for i in range(n_days)]
    solver = Solver()

    # Each day must be a valid city
    for d in day:
        solver.add(And(d >= 0, d < n_cities))

    # Transition constraints
    for i in range(n_days - 1):
        current = day[i]
        next_day = day[i + 1]
        solver.add(Or(
            current == next_day,
            Or([And(current == f, next_day == t) for f, t in transitions])
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

    # Brussels: 2 days (including days 26-27)
    brussels = city_map['Brussels']
    solver.add(Sum([If(day[i] == brussels, 1, 0) for i in range(n_days)]) == 2)
    solver.add(day[25] == brussels)  # Day 26 (0-based index 25)
    solver.add(day[26] == brussels)  # Day 27 (0-based index 26)

    # Madrid: 4 days
    madrid = city_map['Madrid']
    solver.add(Sum([If(day[i] == madrid, 1, 0) for i in range(n_days)]) == 4)

    # Vilnius: 4 days between days 20-23
    vilnius = city_map['Vilnius']
    solver.add(Sum([If(day[i] == vilnius, 1, 0) for i in range(n_days)]) == 4)
    solver.add(Or([day[i] == vilnius for i in range(19, 23)]))

    # Venice: 5 days with workshop between days 7-11
    venice = city_map['Venice']
    solver.add(Sum([If(day[i] == venice, 1, 0) for i in range(n_days)]) == 5)
    solver.add(Or([day[i] == venice for i in range(6, 11)]))

    # Geneva: 4 days with relatives between days 1-4
    geneva = city_map['Geneva']
    solver.add(Sum([If(day[i] == geneva, 1, 0) for i in range(n_days)]) == 4)
    solver.add(Or([day[i] == geneva for i in range(4)]))

    # Munich: 5 days
    munich = city_map['Munich']
    solver.add(Sum([If(day[i] == munich, 1, 0) for i in range(n_days)]) == 5)

    # Reykjavik: 2 days
    reykjavik = city_map['Reykjavik']
    solver.add(Sum([If(day[i] == reykjavik, 1, 0) for i in range(n_days)]) == 2)

    # Solve and format output
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            city_idx = model.evaluate(day[i]).as_long()
            itinerary.append({"day": i + 1, "city": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))