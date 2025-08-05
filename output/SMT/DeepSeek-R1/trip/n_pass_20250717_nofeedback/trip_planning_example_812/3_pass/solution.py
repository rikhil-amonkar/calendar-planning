from z3 import *
import json

# Define the City datatype
City = Datatype('City')
City.declare('Paris')
City.declare('Florence')
City.declare('Vienna')
City.declare('Porto')
City.declare('Munich')
City.declare('Nice')
City.declare('Warsaw')
City = City.create()

# List of all cities
all_cities = [City.Paris, City.Florence, City.Vienna, City.Porto, City.Munich, City.Nice, City.Warsaw]

# Direct flights as tuples (both directions included)
pairs = [
    (City.Florence, City.Vienna),
    (City.Paris, City.Warsaw),
    (City.Munich, City.Vienna),
    (City.Porto, City.Vienna),
    (City.Warsaw, City.Vienna),
    (City.Florence, City.Munich),
    (City.Munich, City.Warsaw),
    (City.Munich, City.Nice),
    (City.Warsaw, City.Nice),
    (City.Porto, City.Munich),
    (City.Porto, City.Nice),
    (City.Paris, City.Vienna),
    (City.Nice, City.Vienna),
    (City.Porto, City.Paris),
    (City.Paris, City.Nice),
    (City.Paris, City.Munich),
    (City.Porto, City.Warsaw)
]

direct_flights_set = set()
for (a, b) in pairs:
    direct_flights_set.add((a, b))
    direct_flights_set.add((b, a))

# Create Z3 solver
solver = Solver()

# Create city_end variables for 20 days: index 1 to 20
city_end = [None]  # index 0 unused
for d in range(1, 21):
    var_name = 'city_end_%d' % d
    city_end.append(Const(var_name, City))

# Constraint: Start in Porto on day 1
solver.add(city_end[1] == City.Porto)

# Define visited[d][c] for each day d and each city c
visited = {}
for d in range(1, 21):
    for c in all_cities:
        if d == 1:
            # On day 1, only the end city is visited
            visited[d, c] = (city_end[d] == c)
        else:
            # On other days, the city is visited if it is the end city of that day or the end city of the previous day (and we flew out of it on this day)
            visited[d, c] = Or(city_end[d] == c, And(city_end[d-1] == c, city_end[d] != city_end[d-1]))

# Fixed constraints: Porto on days 1,2,3
for d in [1,2,3]:
    solver.add(visited[d, City.Porto] == True)

# Fixed constraints: Warsaw on days 13,14,15
for d in [13,14,15]:
    solver.add(visited[d, City.Warsaw] == True)

# Fixed constraints: Vienna on days 19,20
for d in [19,20]:
    solver.add(visited[d, City.Vienna] == True)

# Total days per city
total_days = {}
for city in all_cities:
    total_days[city] = 0
    for d in range(1,21):
        total_days[city] += If(visited[d, city], 1, 0)

solver.add(total_days[City.Paris] == 5)
solver.add(total_days[City.Florence] == 3)
solver.add(total_days[City.Vienna] == 2)
solver.add(total_days[City.Porto] == 3)
solver.add(total_days[City.Munich] == 5)
solver.add(total_days[City.Nice] == 5)
solver.add(total_days[City.Warsaw] == 3)

# Flight constraints: for days 2 to 20, if city_end changes, the pair must be in direct_flights_set
for d in range(2, 21):
    c_prev = city_end[d-1]
    c_curr = city_end[d]
    # If the end city changes from previous day to current day, then the pair must be in the direct_flights_set
    cond = (c_prev != c_curr)
    allowed_pairs = []
    for (c1, c2) in direct_flights_set:
        allowed_pairs.append(And(c_prev == c1, c_curr == c2))
    solver.add(Implies(cond, Or(allowed_pairs)))

# Check and get model
if solver.check() == sat:
    m = solver.model()
    itinerary = []
    for d in range(1, 21):
        for city in all_cities:
            if is_true(m.eval(visited[d, city])):
                city_name = str(city)
                itinerary.append({"day": d, "place": city_name})
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")