from z3 import *
import json

# City indices: 0: Hamburg, 1: Munich, 2: Manchester, 3: Lyon, 4: Split
cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]

n = 20
days = [Int(f"day_{i+1}") for i in range(n)]
solver = Solver()

# Every day the itinerary must be one of the 5 cities (0..4)
for d in days:
    solver.add(And(d >= 0, d < 5))

# Fixed-date constraints:
# (a) Visit Manchester between day 19 and day 20  --> days 19 & 20 must be Manchester (index 2)
solver.add(days[18] == 2)
solver.add(days[19] == 2)

# (b) Annual show in Lyon from day 13 to day 14.
# We force day 13 to be Lyon (index 3) and force a flight on day 14 (so that the departure from Lyon gives Lyon its bonus)
solver.add(days[12] == 3)
solver.add(days[13] != 3)

# Flight rules: if the city changes from day i-1 to day i, then the change must be allowed.
for i in range(1, n):
    # no flight if the same city
    no_flight = (days[i] == days[i-1])
    # if there is a flight then the allowed transitions are:
    flight_from_Hamburg = And(days[i-1] == 0, Or(days[i] == 1, days[i] == 2, days[i] == 4))
    flight_from_Munich   = And(days[i-1] == 1, Or(days[i] == 0, days[i] == 2, days[i] == 3, days[i] == 4))
    flight_from_Manchester = And(days[i-1] == 2, Or(days[i] == 0, days[i] == 1, days[i] == 4))
    flight_from_Lyon = And(days[i-1] == 3, Or(days[i] == 1, days[i] == 4))  # From Lyon: to Munich or Split.
    flight_from_Split = And(days[i-1] == 4, Or(days[i] == 0, days[i] == 1, days[i] == 3))
    solver.add(Or(no_flight, flight_from_Hamburg, flight_from_Munich,
                  flight_from_Manchester, flight_from_Lyon, flight_from_Split))

# Exactly 4 flights must occur – each flight day is when day i != day i–1.
flight_count = Sum([If(days[i] != days[i-1], 1, 0) for i in range(1, n)])
solver.add(flight_count == 4)

# City-day “count” constraints.
# For each day i, the itinerary “assigns” one raw day to the city.
# In addition, if on a day i (i>=2) you fly (i.e. days[i] != days[i-1]),
# then the departure city (day i-1) gets an extra bonus day.
# Thus, for each city c we require:
#    (raw count of days where city == c)
#  + (for each flight day, 1 if the day before was city c)
#  == required count.
#
# Required counts (given in the problem):
#   Hamburg: 7, Munich: 6, Manchester: 2, Lyon: 2, Split: 7.
required = [7, 6, 2, 2, 7]
for c in range(5):
    raw_count = Sum([If(days[i] == c, 1, 0) for i in range(n)])
    bonus = Sum([If(And(days[i] != days[i-1], days[i-1] == c), 1, 0) for i in range(1, n)])
    solver.add(raw_count + bonus == required[c])

# Solve the model.
if solver.check() == sat:
    m = solver.model()
    itinerary = []
    for i in range(n):
        day_city = cities[m[days[i]].as_long()]
        itinerary.append({"day": i+1, "city": day_city})
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")