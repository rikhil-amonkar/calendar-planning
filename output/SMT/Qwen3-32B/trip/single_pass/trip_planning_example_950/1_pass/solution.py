from z3 import *

# Define the cities for C1 to C4 (Mykonos=1, Riga=2, Bucharest=4, Nice=5)
C1, C2, C3, C4 = Ints('C1 C2 C3 C4')
cities = [C1, C2, C3, C4]
allowed_cities = [1, 2, 4, 5]  # Mykonos, Riga, Bucharest, Nice

solver = Solver()

# Add constraints: each city is in allowed_cities and all distinct
for c in cities:
    solver.add(Or([c == val for val in allowed_cities]))
solver.add(Distinct(cities))

# Add constraints for consecutive direct flights
allowed_pairs = [
    (2, 4), (4, 2),  # Riga-Bucharest
    (1, 5), (5, 1),  # Mykonos-Nice
    (2, 5), (5, 2),  # Riga-Nice
    (5, 3), (3, 5),  # Nice-Munich
    (2, 3), (3, 2),  # Riga-Munich
    (4, 3), (3, 4),  # Bucharest-Munich
    (1, 3), (3, 1),  # Mykonos-Munich
]

for i in range(3):  # Check C1-C2, C2-C3, C3-C4
    a, b = cities[i], cities[i+1]
    constraints = []
    for (x, y) in allowed_pairs:
        constraints.append(And(a == x, b == y))
    solver.add(Or(*constraints))

# Define durations for each city
d1 = If(C1 == 1, 3, If(C1 == 2, 3, If(C1 == 4, 4, 3)))
d2 = If(C2 == 1, 3, If(C2 == 2, 3, If(C2 == 4, 4, 3)))
d3 = If(C3 == 1, 3, If(C3 == 2, 3, If(C3 == 4, 4, 3)))
d4 = If(C4 == 1, 3, If(C4 == 2, 3, If(C4 == 4, 4, 3)))

# Add Mykonos overlap constraints
solver.add(Implies(C2 == 1, And(3 + d1 <= 6, 2 + d1 + d2 >= 4)))
solver.add(Implies(C3 == 1, And(2 + d1 + d2 <= 6, 1 + d1 + d2 + d3 >= 4)))
solver.add(Implies(C4 == 1, And(1 + d1 + d2 + d3 <= 6, d1 + d2 + d3 + d4 >= 4)))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    c_values = [model.eval(c).as_long() for c in cities]
    city_order = [0] + c_values + [3, 6]  # Rome, C1-C4, Munich, Krakow
    durations = {
        0: 4,  # Rome
        1: 3,  # Mykonos
        2: 3,  # Riga
        3: 4,  # Munich
        4: 4,  # Bucharest
        5: 3,  # Nice
        6: 2,  # Krakow
    }

    start_days = [1]
    end_days = [start_days[0] + durations[city_order[0]] - 1]

    for i in range(1, len(city_order)):
        start_days.append(end_days[-1])
        end_days.append(start_days[-1] + durations[city_order[i]] - 1)

    day_to_city = {}
    for i in range(len(city_order)):
        city = city_order[i]
        start = start_days[i]
        end = end_days[i]
        for day in range(start, end + 1):
            day_to_city[day] = city

    city_names = {
        0: 'Rome',
        1: 'Mykonos',
        2: 'Riga',
        3: 'Munich',
        4: 'Bucharest',
        5: 'Nice',
        6: 'Krakow'
    }

    itinerary_list = []
    for day in sorted(day_to_city.keys()):
        city = day_to_city[day]
        itinerary_list.append({day: city_names[city]})

    result = {
        'itinerary': itinerary_list
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")