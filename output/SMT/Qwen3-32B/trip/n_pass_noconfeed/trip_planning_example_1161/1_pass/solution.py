import z3
import json

# Define cities and their indices
cities = ['Oslo', 'Dubrovnik', 'Krakow', 'Vilnius', 'Helsinki', 'Madrid', 'Paris', 'Mykonos']
direct_flights = set([
    (0, 2), (2, 0),
    (0, 6), (6, 0),
    (6, 5), (5, 6),
    (4, 3), (3, 4),
    (0, 5), (5, 0),
    (0, 4), (4, 0),
    (4, 2), (2, 4),
    (1, 4), (4, 1),
    (1, 5), (5, 1),
    (0, 1), (1, 0),
    (2, 3), (3, 2),
    (4, 6), (6, 4),
    (3, 6), (6, 3),
    (4, 5), (5, 4),
    (5, 7), (7, 5),
])

durations = [2, 3, 5, 2, 2, 5, 2, 4]  # index 0-7

s = z3.Solver()

# Positions 2-7 (indices 2-7 in the sequence)
pos2 = z3.Int('pos2')
pos3 = z3.Int('pos3')
pos4 = z3.Int('pos4')
pos5 = z3.Int('pos5')
pos6 = z3.Int('pos6')
pos7 = z3.Int('pos7')

positions = [pos2, pos3, pos4, pos5, pos6, pos7]

# All positions 2-7 must be in {2,3,4,5,6,7} and distinct
allowed_cities = [2, 3, 4, 5, 6, 7]
s.add(z3.Distinct(positions))
for p in positions:
    s.add(z3.Or([p == city for city in allowed_cities]))

# Consecutive direct flights
s.add(z3.Or([(1, pos2) in direct_flights, (pos2, 1) in direct_flights]))
s.add(z3.Or([(pos2, pos3) in direct_flights, (pos3, pos2) in direct_flights]))
s.add(z3.Or([(pos3, pos4) in direct_flights, (pos4, pos3) in direct_flights]))
s.add(z3.Or([(pos4, pos5) in direct_flights, (pos5, pos4) in direct_flights]))
s.add(z3.Or([(pos5, pos6) in direct_flights, (pos6, pos5) in direct_flights]))
s.add(z3.Or([(pos6, pos7) in direct_flights, (pos7, pos6) in direct_flights]))

# Define get_duration function
def get_duration(city_var):
    return z3.If(city_var == 2, 5,
                 z3.If(city_var == 3, 2,
                      z3.If(city_var == 4, 2,
                           z3.If(city_var == 5, 5,
                                z3.If(city_var == 6, 2, 4)))))

# Compute start_day expressions
start_day_expr = [0] * 8
start_day_expr[0] = 1
start_day_expr[1] = 2  # 1 + durations[0] - 1 = 1+2-1=2
start_day_expr[2] = 4  # start_day_expr[1] + durations[1] -1 = 2 +3-1=4

start_day_expr[3] = start_day_expr[2] + get_duration(pos2) - 1
start_day_expr[4] = start_day_expr[3] + get_duration(pos3) - 1
start_day_expr[5] = start_day_expr[4] + get_duration(pos4) - 1
start_day_expr[6] = start_day_expr[5] + get_duration(pos5) - 1
start_day_expr[7] = start_day_expr[6] + get_duration(pos6) - 1

# Constraint for last day
s.add(start_day_expr[7] + get_duration(pos7) - 1 == 18)

# Constraints for Mykonos
for i in range(2, 8):
    if i == 2:
        city_var = pos2
    elif i == 3:
        city_var = pos3
    elif i == 4:
        city_var = pos4
    elif i == 5:
        city_var = pos5
    elif i == 6:
        city_var = pos6
    elif i == 7:
        city_var = pos7
    s.add(z3.Implies(start_day_expr[i] == 15, city_var == 7))

# Solve
if s.check() == z3.sat:
    model = s.model()
    pos_values = [model.eval(p) for p in positions]
    sequence = [0, 1] + [int(str(p)) for p in pos_values]
    start_days = [0] * 8
    start_days[0] = 1
    start_days[1] = 2
    start_days[2] = 4
    for i in range(3, 8):
        prev_city = sequence[i-1]
        duration_prev = durations[prev_city]
        start_days[i] = start_days[i-1] + duration_prev - 1

    itinerary = []
    for i in range(8):
        city = sequence[i]
        start = start_days[i]
        duration = durations[city]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": cities[city]})

    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")