from z3 import Solver, Int, Distinct, If, And, Or, Implies, sat
import json

# City definitions (index: city_name, required days)
cities = {
    0: {"name": "Venice",      "days": 3},
    1: {"name": "Reykjavik",    "days": 2},
    2: {"name": "Munich",       "days": 3},  # must contain days 4-6 => S == 4 then end = 6
    3: {"name": "Santorini",    "days": 3},  # must intersect days 8-10 => start between 6 and 10
    4: {"name": "Manchester",   "days": 3},
    5: {"name": "Porto",        "days": 3},
    6: {"name": "Bucharest",    "days": 5},
    7: {"name": "Tallinn",      "days": 4},
    8: {"name": "Valencia",     "days": 2},  # must include workshop day: block must include either day 14 or 15
    9: {"name": "Vienna",       "days": 5}
}

# Allowed flight connections (use canonical ordering for unordered pairs)
allowed_edges = [
    (0,2), (0,3), (0,4), (0,9),
    (1,2), (1,9),
    (2,4), (2,5), (2,6), (2,7), (2,8), (2,9),
    (3,4), (3,6), (3,9),
    (4,5), (4,6), (4,9),
    (5,8), (5,9),
    (6,8), (6,9),
    (8,9)
]

# Helper: given a city (as a Z3 expression) return its required days.
def get_duration(city):
    return If(city == 0, cities[0]["days"],
           If(city == 1, cities[1]["days"],
           If(city == 2, cities[2]["days"],
           If(city == 3, cities[3]["days"],
           If(city == 4, cities[4]["days"],
           If(city == 5, cities[5]["days"],
           If(city == 6, cities[6]["days"],
           If(city == 7, cities[7]["days"],
           If(city == 8, cities[8]["days"],
              cities[9]["days"]))))))))

# Create solver instance
solver = Solver()

# We create 10 integer variables for the permutation of cities (each value 0...9)
perm = [Int(f"perm_{i}") for i in range(10)]
solver.add(Distinct(perm))
for i in range(10):
    solver.add(perm[i] >= 0, perm[i] <= 9)

# Create a list S[0..9] for the start day of each city’s block.
S = [Int(f"S_{i}") for i in range(10)]
# First city must start on day 1.
solver.add(S[0] == 1)

# For each city block in the itinerary, the block is from S_i to d_i = S_i + (duration-1).
# Also, when flying from position i to i+1 the flight day is S[i+1] (which is the same as d_i).
for i in range(1, 10):
    # S[i] = S[i-1] + (duration of city at position i-1) - 1.
    solver.add(S[i] == S[i-1] + (get_duration(perm[i-1]) - 1))

# Total timeline must be 24 days.
# For the last city: d_last = S[9] + (duration - 1) must equal 24.
solver.add(S[9] + get_duration(perm[9]) - 1 == 24)

# Special day constraints (applied to whichever position a city appears)
for i in range(10):
    # If the city in position i is Munich (index 2) then its start must be exactly 4 (so its block is days 4-6).
    solver.add(Implies(perm[i] == 2, S[i] == 4))
    # If Santorini (index 3), then we require its 3–day interval [S, S+2] to catch a day between 8 and 10.
    # A sufficient condition is: S[i] <= 10 and S[i]+2 >= 8 (i.e. S[i] >= 6).
    solver.add(Implies(perm[i] == 3, And(S[i] >= 6, S[i] <= 10)))
    # If Valencia (index 8), then its 2–day interval [S, S+1] must include either day 14 or day 15.
    # (That forces S[i] to be either 13, 14 or 15.)
    solver.add(Implies(perm[i] == 8, Or(S[i] == 13, S[i] == 14, S[i] == 15)))

# Flight constraints: consecutive cities in the permutation must have a direct flight.
for i in range(9):
    p = perm[i]
    q = perm[i+1]
    # For each allowed edge (a, b), we allow either (p == a and q == b) or (p == b and q == a).
    flight_ok = []
    for (a, b) in allowed_edges:
        flight_ok.append(Or(And(p == a, q == b), And(p == b, q == a)))
    solver.add(Or(flight_ok))

# Solve the constraints
if solver.check() == sat:
    m = solver.model()
    # Build the itinerary: for each city block (in order) record the city name and block interval.
    itinerary = []
    for i in range(10):
        # Evaluate city index and start day.
        city_index = m.evaluate(perm[i]).as_long()
        start_day = m.evaluate(S[i]).as_long()
        duration = m.evaluate(get_duration(perm[i])).as_long()
        end_day = start_day + duration - 1
        itinerary.append({
            "city": cities[city_index]["name"],
            "start_day": start_day,
            "end_day": end_day
        })
    # Output the itinerary as JSON.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")