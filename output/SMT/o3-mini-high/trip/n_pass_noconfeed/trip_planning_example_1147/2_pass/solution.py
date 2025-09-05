from z3 import Solver, Int, If, And, Or, Distinct, sat, Implies
import json

# City indices:
# 0: Istanbul, 1: Brussels, 2: Helsinki, 3: Split, 4: Dubrovnik, 5: Milan, 6: Vilnius, 7: Frankfurt
city_names = {
    0: "Istanbul",
    1: "Brussels",
    2: "Helsinki",
    3: "Split",
    4: "Dubrovnik",
    5: "Milan",
    6: "Vilnius",
    7: "Frankfurt"
}

# Required durations for each city (in days)
# Note: When a city is not the last city visited, the flight day counts for both cities.
city_duration = {
    0: 5,  # Istanbul
    1: 3,  # Brussels
    2: 3,  # Helsinki
    3: 4,  # Split
    4: 2,  # Dubrovnik
    5: 4,  # Milan
    6: 5,  # Vilnius
    7: 3   # Frankfurt
}

def duration_expr(city_var):
    return If(city_var == 0, city_duration[0],
           If(city_var == 1, city_duration[1],
           If(city_var == 2, city_duration[2],
           If(city_var == 3, city_duration[3],
           If(city_var == 4, city_duration[4],
           If(city_var == 5, city_duration[5],
           If(city_var == 6, city_duration[6],
           If(city_var == 7, city_duration[7], 0))))))))   # Added extra closing parenthesis

# Allowed direct flights (edges). 
# For bidirectional flights, both directions are added.
# For one-way flights, only the specified direction is allowed.
allowed_flights = [
    (5, 7), (7, 5),      # Milan and Frankfurt
    (3, 7), (7, 3),      # Split and Frankfurt
    (5, 3), (3, 5),      # Milan and Split
    (1, 6), (6, 1),      # Brussels and Vilnius
    (1, 2), (2, 1),      # Brussels and Helsinki
    (0, 1), (1, 0),      # Istanbul and Brussels
    (5, 6), (6, 5),      # Milan and Vilnius
    (1, 5), (5, 1),      # Brussels and Milan
    (0, 2), (2, 0),      # Istanbul and Helsinki
    (2, 6), (6, 2),      # Helsinki and Vilnius
    (2, 4), (4, 2),      # Helsinki and Dubrovnik
    (3, 6), (6, 3),      # Split and Vilnius
    (4, 0),             # from Dubrovnik to Istanbul (one-way)
    (0, 5), (5, 0),      # Istanbul and Milan
    (2, 7), (7, 2),      # Helsinki and Frankfurt
    (0, 6), (6, 0),      # Istanbul and Vilnius
    (3, 2), (2, 3),      # Split and Helsinki
    (5, 2), (2, 5),      # Milan and Helsinki
    (0, 7), (7, 0),      # Istanbul and Frankfurt
    (1, 7),             # from Brussels to Frankfurt (one-way)
    (4, 7), (7, 4),      # Dubrovnik and Frankfurt
    (7, 6), (6, 7)       # Frankfurt and Vilnius
]

solver = Solver()

# Create 8 integer variables for the itinerary order.
# pos[i] represents the city index at the i-th segment (0-indexed).
pos = [Int(f"pos_{i}") for i in range(8)]
for p in pos:
    solver.add(And(p >= 0, p < 8))
solver.add(Distinct(pos))
# Istanbul must be the first city (to attend the Istanbul show from day 1 to 5)
solver.add(pos[0] == 0)

# Create variables for the start day (S[i]) of each segment.
# The itinerary is defined such that if a flight is taken on day X,
# that day is counted for both cities (thus segments overlap at the transition).
S = [Int(f"S_{i}") for i in range(8)]
solver.add(S[0] == 1)  # Trip starts on Day 1

# For each segment, the end day E[i] is S[i] + duration - 1.
# And the next segment starts on the same day as the previous segment's end day.
for i in range(1, 8):
    solver.add(S[i] == S[i-1] + (duration_expr(pos[i-1]) - 1))
# The trip must end on Day 22.
solver.add(S[7] + duration_expr(pos[7]) - 1 == 22)

# Add flight connectivity constraints between consecutive cities.
for i in range(7):
    a = pos[i]
    b = pos[i+1]
    flight_possible = []
    for (u, v) in allowed_flights:
        flight_possible.append(And(a == u, b == v))
    solver.add(Or(*flight_possible))

# Constraint: Wedding in Frankfurt between Day 16 and 18.
# If Frankfurt (city 7) is visited in segment i, its day range [S, S + 3 - 1] must intersect [16,18].
for i in range(8):
    solver.add(Implies(pos[i] == 7, And(S[i] <= 18, S[i] + city_duration[7] - 1 >= 16)))
    
# Constraint: Workshop in Vilnius between Day 18 and 22.
# If Vilnius (city 6) is visited, its day range [S, S + 5 - 1] must intersect [18,22].
for i in range(8):
    solver.add(Implies(pos[i] == 6, And(S[i] <= 22, S[i] + city_duration[6] - 1 >= 18)))

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(8):
        city_id = model.eval(pos[i]).as_long()
        start_day = model.eval(S[i]).as_long()
        d = city_duration[city_id]
        end_day = start_day + d - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_names[city_id]})
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))