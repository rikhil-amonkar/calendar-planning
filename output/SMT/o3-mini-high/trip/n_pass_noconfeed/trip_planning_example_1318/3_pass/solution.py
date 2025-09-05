#!/usr/bin/env python3
from z3 import *
import json

# Mapping city names to indices:
# 0: Oslo, 1: Helsinki, 2: Edinburgh, 3: Riga, 4: Tallinn, 5: Budapest,
# 6: Vilnius, 7: Porto, 8: Geneva
city_names = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn",
              "Budapest", "Vilnius", "Porto", "Geneva"]

# Fixed durations for each city
durations = {
    0: 2,  # Oslo
    1: 2,  # Helsinki
    2: 3,  # Edinburgh
    3: 2,  # Riga
    4: 5,  # Tallinn
    5: 5,  # Budapest
    6: 5,  # Vilnius
    7: 5,  # Porto
    8: 4   # Geneva
}

# Allowed direct flights.
# For "CityA and CityB", add both directions.
# For flights specified as "from X to Y", include only that ordered pair.
allowed_flights = [
    (7, 0), (0, 7),            # Porto <-> Oslo
    (2, 5), (5, 2),            # Edinburgh <-> Budapest
    (2, 8), (8, 2),            # Edinburgh <-> Geneva
    (3, 4),                   # from Riga to Tallinn (directed)
    (2, 7), (7, 2),            # Edinburgh <-> Porto
    (6, 1), (1, 6),            # Vilnius <-> Helsinki
    (4, 6),                   # from Tallinn to Vilnius (directed)
    (3, 0), (0, 3),            # Riga <-> Oslo
    (8, 0), (0, 8),            # Geneva <-> Oslo
    (2, 0), (0, 2),            # Edinburgh <-> Oslo
    (2, 1), (1, 2),            # Edinburgh <-> Helsinki
    (6, 0), (0, 6),            # Vilnius <-> Oslo
    (3, 1), (1, 3),            # Riga <-> Helsinki
    (5, 8), (8, 5),            # Budapest <-> Geneva
    (1, 5), (5, 1),            # Helsinki <-> Budapest
    (1, 0), (0, 1),            # Helsinki <-> Oslo
    (2, 3), (3, 2),            # Edinburgh <-> Riga
    (4, 1), (1, 4),            # Tallinn <-> Helsinki
    (8, 7), (7, 8),            # Geneva <-> Porto
    (5, 0), (0, 5),            # Budapest <-> Oslo
    (1, 8), (8, 1),            # Helsinki <-> Geneva
    (3, 6),                   # from Riga to Vilnius (directed)
    (4, 0), (0, 4)             # Tallinn <-> Oslo
]

# Helper function that returns a Z3 expression for the duration in a city.
# Using Sum([If(...)]) forces exactly one of the clauses to contribute its duration.
def duration_expr(city_var):
    return Sum([If(city_var == i, durations[i], 0) for i in range(9)])

# Create the solver
solver = Solver()

n_cities = 9  # total cities in the itinerary

# Create variables: itinerary positions and start days for each city's segment.
itinerary = [Int("city_%d" % i) for i in range(n_cities)]
S = [Int("S_%d" % i) for i in range(n_cities)]  # S[i] is the start day for the i-th visited city

# Domain constraints for itinerary: each city index must be between 0 and 8 and all must be distinct.
for i in range(n_cities):
    solver.add(itinerary[i] >= 0, itinerary[i] <= 8)
solver.add(Distinct(itinerary))

# Set the start day for the first city to day 1, and each start day is between 1 and 25.
solver.add(S[0] == 1)
for i in range(n_cities):
    solver.add(S[i] >= 1, S[i] <= 25)

# Transition constraints for the schedule:
# The i-th city is visited from day S[i] to S[i] + duration - 1. The next city’s segment
# starts on the last day of the previous city’s trip.
for i in range(n_cities - 1):
    solver.add(S[i+1] == S[i] + duration_expr(itinerary[i]) - 1)
# The last city must finish on day 25.
solver.add(S[n_cities - 1] + duration_expr(itinerary[n_cities - 1]) - 1 == 25)

# Flight connection constraints:
# For each consecutive pair of cities, there must be an allowed direct flight.
for i in range(n_cities - 1):
    possible_flights = []
    for (p, q) in allowed_flights:
        possible_flights.append(And(itinerary[i] == p, itinerary[i+1] == q))
    solver.add(Or(possible_flights))

# Special scheduling constraints:
# 1. In Oslo (city 0) the friend meeting must happen between day 24 and day 25.
#    (Since Oslo’s duration is 2 days, its segment runs from S[i] to S[i]+1.)
for i in range(n_cities):
    friend_constraint = Or(
        And(S[i] <= 24, 24 <= S[i] + 2 - 1),
        And(S[i] <= 25, 25 <= S[i] + 2 - 1)
    )
    solver.add(Implies(itinerary[i] == 0, friend_constraint))

# 2. In Tallinn (city 4) the wedding must occur between day 4 and day 8.
#    (Tallinn’s duration is 5 days so its segment runs from S[i] to S[i]+4.)
for i in range(n_cities):
    wedding_constraint = Or(
        And(S[i] <= 4, 4 <= S[i] + 5 - 1),
        And(S[i] <= 5, 5 <= S[i] + 5 - 1),
        And(S[i] <= 6, 6 <= S[i] + 5 - 1),
        And(S[i] <= 7, 7 <= S[i] + 5 - 1),
        And(S[i] <= 8, 8 <= S[i] + 5 - 1)
    )
    solver.add(Implies(itinerary[i] == 4, wedding_constraint))

# Check for a solution.
if solver.check() == sat:
    model = solver.model()
    itinerary_plan = []
    for i in range(n_cities):
        city_index = model.evaluate(itinerary[i]).as_long()
        start_day = model.evaluate(S[i]).as_long()
        dur = durations[city_index]
        end_day = start_day + dur - 1
        itinerary_plan.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_index]
        })
    output = {"itinerary": itinerary_plan}
    print(json.dumps(output))
else:
    print(json.dumps({"error": "No itinerary found satisfying all constraints."}))