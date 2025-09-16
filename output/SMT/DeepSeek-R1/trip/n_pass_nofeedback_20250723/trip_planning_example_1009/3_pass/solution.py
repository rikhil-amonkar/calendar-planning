from z3 import *
import json

# Define the City datatype
City = Datatype('City')
city_list = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
for c in city_list:
    City.declare(c)
City = City.create()

# Define the directed flight graph
bidirectional_pairs = [
    ("Bucharest", "Vienna"),
    ("Reykjavik", "Vienna"),
    ("Manchester", "Vienna"),
    ("Manchester", "Riga"),
    ("Riga", "Vienna"),
    ("Istanbul", "Vienna"),
    ("Vienna", "Florence"),
    ("Stuttgart", "Vienna"),
    ("Riga", "Bucharest"),
    ("Istanbul", "Riga"),
    ("Stuttgart", "Istanbul"),
    ("Istanbul", "Bucharest"),
    ("Manchester", "Istanbul"),
    ("Manchester", "Bucharest"),
    ("Stuttgart", "Manchester")
]

directed_edges = set()
for (u, v) in bidirectional_pairs:
    directed_edges.add((u, v))
    directed_edges.add((v, u))
directed_edges.add(("Reykjavik", "Stuttgart"))

# Convert to City datatype
directed_edges_city = set()
for (u_str, v_str) in directed_edges:
    u_city = getattr(City, u_str)
    v_city = getattr(City, v_str)
    directed_edges_city.add((u_city, v_city))

# Required days for each city
days_req = {
    "Riga": 4,
    "Manchester": 5,
    "Bucharest": 4,
    "Florence": 4,
    "Vienna": 2,
    "Istanbul": 2,
    "Reykjavik": 4,
    "Stuttgart": 5
}

# Initialize solver
solver = Solver()

# Create variables: sequence of cities, start days, end days
c = [Const(f'c_{i}', City) for i in range(8)]
s = [Int(f's_{i}') for i in range(8)]
e = [Int(f'e_{i}') for i in range(8)]

# Constraint: distinct cities
solver.add(Distinct(c))

# Constraints for start and end days
solver.add(s[0] == 1)
solver.add(e[7] == 23)

# Define a function for days required
days_func = Function('days_func', City, IntSort())
for city_name, days in days_req.items():
    city_val = getattr(City, city_name)
    solver.add(days_func(city_val) == days)

for i in range(8):
    # Duration constraint: e[i] = s[i] + days - 1
    solver.add(e[i] == s[i] + days_func(c[i]) - 1)
    
    # Chain the cities: end of current city is start of next
    if i < 7:
        solver.add(s[i+1] == e[i])
    
    # Day bounds
    solver.add(s[i] >= 1)
    solver.add(s[i] <= 23)
    solver.add(e[i] >= 1)
    solver.add(e[i] <= 23)

# Flight constraints between consecutive cities
for i in range(7):
    u = c[i]
    v = c[i+1]
    solver.add(Or([And(u == u_val, v == v_val) for (u_val, v_val) in directed_edges_city]))

# Special constraints for Istanbul and Bucharest
for i in range(8):
    solver.add(Implies(c[i] == City.Istanbul, s[i] == 12))
    solver.add(Implies(c[i] == City.Bucharest, s[i] == 16))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    c_val = [model.evaluate(c[i]) for i in range(8)]
    s_val = [model.evaluate(s[i]).as_long() for i in range(8)]
    e_val = [model.evaluate(e[i]).as_long() for i in range(8)]
    
    # Map city to its name
    city_names = {getattr(City, name): name for name in city_list}
    c_names = [city_names[c_val[i]] for i in range(8)]
    
    # Build itinerary
    itinerary = []
    for d in range(1, 24):  # days 1 to 23
        current_cities = []
        for i in range(8):
            if s_val[i] <= d <= e_val[i]:
                current_cities.append(c_names[i])
        current_cities.sort()  # for consistent ordering
        place_str = " and ".join(current_cities)
        itinerary.append({"day": d, "place": place_str})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")