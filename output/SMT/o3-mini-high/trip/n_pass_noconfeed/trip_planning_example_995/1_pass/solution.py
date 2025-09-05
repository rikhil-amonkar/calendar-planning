from z3 import *
import json

# Cities: indices mapped to names.
cities = ["Oslo", "Stuttgart", "Venice", "Split", "Barcelona", "Brussels", "Copenhagen"]

# Duration mapping for each city.
# Oslo:2, Stuttgart:3, Venice:4, Split:4, Barcelona:3, Brussels:3, Copenhagen:3
durations = {"Oslo": 2, "Stuttgart": 3, "Venice": 4, "Split": 4, "Barcelona": 3, "Brussels": 3, "Copenhagen": 3}

# Helper function: Given a Z3 expression for a city index, return its duration.
def Duration(city):
    return If(city == 0, 2,
           If(city == 1, 3,
           If(city == 2, 4,
           If(city == 3, 4,
           If(city == 4, 3,
           If(city == 5, 3, 3))))))

# Allowed direct flights (bidirectional).
allowed_pairs = [
    (2, 1), (1, 2),      # Venice and Stuttgart
    (0, 5), (5, 0),      # Oslo and Brussels
    (3, 6), (6, 3),      # Split and Copenhagen
    (4, 6), (6, 4),      # Barcelona and Copenhagen
    (4, 2), (2, 4),      # Barcelona and Venice
    (5, 2), (2, 5),      # Brussels and Venice
    (4, 1), (1, 4),      # Barcelona and Stuttgart
    (6, 5), (5, 6),      # Copenhagen and Brussels
    (0, 3), (3, 0),      # Oslo and Split
    (0, 2), (2, 0),      # Oslo and Venice
    (4, 3), (3, 4),      # Barcelona and Split
    (0, 6), (6, 0),      # Oslo and Copenhagen
    (4, 0), (0, 4),      # Barcelona and Oslo
    (6, 1), (1, 6),      # Copenhagen and Stuttgart
    (3, 1), (1, 3),      # Split and Stuttgart
    (6, 2), (2, 6),      # Copenhagen and Venice
    (4, 5), (5, 4)       # Barcelona and Brussels
]

# Create Z3 solver instance
solver = Solver()

n_cities = 7  # Total cities in the itinerary

# p[i] represents the city visited at position i in the itinerary.
p = [Int(f"p_{i}") for i in range(n_cities)]
# s[i] represents the start day of the visit for the city at position i.
s = [Int(f"s_{i}") for i in range(n_cities)]

# Each city index must be between 0 and 6 and all p[i] must be distinct.
for i in range(n_cities):
    solver.add(p[i] >= 0, p[i] < n_cities)
    solver.add(s[i] >= 1)  # start day cannot be before day 1
solver.add(Distinct(p))

# The trip schedule: s[0] is day 1.
solver.add(s[0] == 1)
# If you fly from city A to B on day X, then you are in both cities on day X.
# That is encoded as: s[i+1] = s[i] + Duration(p[i]) - 1.
for i in range(n_cities - 1):
    solver.add(s[i+1] == s[i] + Duration(p[i]) - 1)

# Total trip days constraint: last city's end day = s[n-1] + Duration(p[n-1]) - 1 equals 16.
solver.add(s[n_cities - 1] + Duration(p[n_cities - 1]) - 1 == 16)

# Flight connection constraints: For each consecutive pair in itinerary, there must be a direct flight.
for i in range(n_cities - 1):
    flight_constraints = []
    for (a, b) in allowed_pairs:
        flight_constraints.append(And(p[i] == a, p[i+1] == b))
    solver.add(Or(flight_constraints))

# Special constraints based on participants' wishes:

# 1. Meet friends in Oslo between day 3 and day 4.
#    If a city is Oslo (index 0), its visit (duration 2 days) covers days s and s+1.
#    It must include day 3 or day 4.
for i in range(n_cities):
    solver.add(Implies(p[i] == 0,
                       Or(And(s[i] <= 3, 3 <= s[i] + 2 - 1),
                          And(s[i] <= 4, 4 <= s[i] + 2 - 1))))

# 2. Attend annual show in Barcelona from day 1 to day 3.
#    If a city is Barcelona (index 4, duration 3 days: days s, s+1, s+2),
#    then the visit must start on or before day 3 so that at least one day (day 1,2 or 3) is included.
for i in range(n_cities):
    solver.add(Implies(p[i] == 4, s[i] <= 3))

# 3. Meet a friend in Brussels between day 9 and day 11.
#    Brussels (index 5, duration 3 days: s, s+1, s+2) must cover at least one of days 9,10,11.
#    This is equivalent to: s[i] <= 11 and s[i] + 3 - 1 >= 9.
for i in range(n_cities):
    solver.add(Implies(p[i] == 5, And(s[i] <= 11, s[i] + 3 - 1 >= 9)))

# (The durations of each city are fixed by design, so no extra constraint is needed.)

# Check if the constraints are satisfiable and compute a model.
if solver.check() == sat:
    m = solver.model()
    itinerary = []
    for i in range(n_cities):
        # Get the city index and corresponding city name.
        city_index = m.evaluate(p[i]).as_long()
        city_name = cities[city_index]
        # Get the start day and compute the end day using the fixed duration.
        start_day = m.evaluate(s[i]).as_long()
        duration = durations[city_name]
        end_day = start_day + duration - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_name
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No valid itinerary found."}))