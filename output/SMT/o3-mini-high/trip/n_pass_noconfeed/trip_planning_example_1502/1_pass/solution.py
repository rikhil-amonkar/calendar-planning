from z3 import *
import json

# Define city properties: each city is represented by an integer (0 to 9)
# with associated name and duration.
city_names = {
    0: "Santorini",
    1: "Valencia",
    2: "Madrid",
    3: "Seville",
    4: "Bucharest",
    5: "Vienna",
    6: "Riga",
    7: "Tallinn",
    8: "Krakow",
    9: "Frankfurt"
}
# Durations for each city (how many days you spend there):
durations = {
    0: 3,
    1: 4,
    2: 2,
    3: 2,
    4: 3,
    5: 4,
    6: 4,
    7: 5,
    8: 5,
    9: 4
}

# SMT version of "duration" function: given a city variable, return its duration.
def city_duration(city):
    return If(city == 0, 3,
           If(city == 1, 4,
           If(city == 2, 2,
           If(city == 3, 2,
           If(city == 4, 3,
           If(city == 5, 4,
           If(city == 6, 4,
           If(city == 7, 5,
           If(city == 8, 5,
           If(city == 9, 4, 0))))))))))

# Allowed direct flights (as ordered pairs). For most, flights are bidirectional.
# Note: The flight "from Riga to Tallinn" is directional (only (6,7) allowed).
allowed_flights = [
    (5, 4), (4, 5),                # Vienna <-> Bucharest
    (0, 2), (2, 0),                # Santorini <-> Madrid
    (3, 1), (1, 3),                # Seville <-> Valencia
    (5, 3), (3, 5),                # Vienna <-> Seville
    (2, 1), (1, 2),                # Madrid <-> Valencia
    (4, 6), (6, 4),                # Bucharest <-> Riga
    (1, 4), (4, 1),                # Valencia <-> Bucharest
    (0, 4), (4, 0),                # Santorini <-> Bucharest
    (5, 1), (1, 5),                # Vienna <-> Valencia
    (5, 2), (2, 5),                # Vienna <-> Madrid
    (1, 8), (8, 1),                # Valencia <-> Krakow
    (1, 9), (9, 1),                # Valencia <-> Frankfurt
    (8, 9), (9, 8),                # Krakow <-> Frankfurt
    (6, 7),                       # from Riga to Tallinn (directional)
    (5, 8), (8, 5),                # Vienna <-> Krakow
    (5, 9), (9, 5),                # Vienna <-> Frankfurt
    (2, 3), (3, 2),                # Madrid <-> Seville
    (0, 5), (5, 0),                # Santorini <-> Vienna
    (5, 6), (6, 5),                # Vienna <-> Riga
    (9, 7), (7, 9),                # Frankfurt <-> Tallinn
    (9, 4), (4, 9),                # Frankfurt <-> Bucharest
    (2, 4), (4, 2),                # Madrid <-> Bucharest
    (9, 6), (6, 9),                # Frankfurt <-> Riga
    (2, 9), (9, 2)                 # Madrid <-> Frankfurt
]

# Create a Z3 solver
solver = Solver()

# We need to decide:
# 1. The order in which the 10 cities are visited.
# 2. The start day (s_i) for each city visit (with overlapping flight days).
# The itinerary is a sequence of 10 segments. For segment i:
#   s[i] is the start day; the city visit lasts for durations[city] days.
#   If you fly from segment i to i+1 on day X, then X is counted in both segments.
# The relation is: s[0] = 1, and for each i from 0 to 8:
#   s[i+1] = s[i] + duration(city at segment i) - 1.
# The final segment ends on day: s[9] + duration(city at segment 9) - 1 = 27.

# Create 10 order variables for the cities (each in 0..9)
order = [Int("order_%d" % i) for i in range(10)]
# Create 10 start day variables (the day the visit for that city starts)
s = [Int("s_%d" % i) for i in range(10)]

# Domain constraints
for i in range(10):
    solver.add(order[i] >= 0, order[i] <= 9)
    solver.add(s[i] >= 1, s[i] <= 27)  # reasonable day range

# All cities must be visited exactly once.
solver.add(Distinct(order))

# Trip timing constraints.
solver.add(s[0] == 1)
for i in range(9):
    solver.add(s[i+1] == s[i] + city_duration(order[i]) - 1)
# The final city must finish on day 27.
solver.add(s[9] + city_duration(order[9]) - 1 == 27)

# Flight connectivity constraints: for each adjacent pair of cities in the itinerary,
# there must be a direct flight.
for i in range(9):
    valid_flights = []
    for (a, b) in allowed_flights:
        valid_flights.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(valid_flights))

# Event / Special-date constraints:
for i in range(10):
    # Madrid (city 2): You plan to stay 2 days in Madrid and attend an annual show
    # from day 6 to day 7; with a 2-day visit it must exactly be: day 6-7.
    solver.add(Implies(order[i] == 2, s[i] == 6))
    
    # Vienna (city 5): You plan to stay 4 days in Vienna and attend a wedding between day 3 and day 6.
    # The Vienna segment is from s to s+3; to include at least one day in [3,6],
    # we force the start to be no later than day 6.
    solver.add(Implies(order[i] == 5, s[i] <= 6))
    
    # Riga (city 6): You want to visit Riga for 4 days and must attend a conference on day 20 and day 23.
    # With a 4-day visit, the only possibility is to start on day 20 (i.e. days 20-23).
    solver.add(Implies(order[i] == 6, s[i] == 20))
    
    # Tallinn (city 7): You want to spend 5 days in Tallinn and attend a workshop between day 23 and day 27.
    # This requires that [s, s+4] has at least one day in [23,27]; a sufficient condition is s[i]+4 >= 23.
    solver.add(Implies(order[i] == 7, s[i] + 4 >= 23))
    
    # Krakow (city 8): You plan to stay 5 days in Krakow and meet your friends between day 11 and day 15.
    # The visit [s, s+4] must overlap with [11,15]. Enforce s[i] <= 15 and s[i] + 4 >= 11.
    solver.add(Implies(order[i] == 8, And(s[i] <= 15, s[i] + 4 >= 11)))

# Solve the SMT model.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Build the itinerary based on the model's order and start days.
    for i in range(10):
        city_id = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(s[i]).as_long()
        dur = durations[city_id]
        end_day = start_day + dur - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_id]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No solution found"}))