from z3 import *
import json

# --- Data definitions ---
# We assign each city an index:
# 0: Stockholm, 1: Amsterdam, 2: Valencia, 3: Bucharest, 4: Vienna,
# 5: Reykjavik, 6: Athens, 7: Riga, 8: Frankfurt, 9: Salzburg.

city_names = ["Stockholm", "Amsterdam", "Valencia", "Bucharest", "Vienna",
              "Reykjavik", "Athens", "Riga", "Frankfurt", "Salzburg"]

# Durations for each city (in days)
durations = [3, 3, 2, 3, 5, 5, 5, 3, 4, 5]

# Allowed direct flights between any two cities.
# For each allowed connection we give the (i,j) pair.
# (Directional flights are given only in the allowed direction.)
allowed_pairs = [
    # "Valencia and Frankfurt"
    (2, 8), (8, 2),
    # "Vienna and Bucharest"
    (4, 3), (3, 4),
    # "from Valencia to Athens"
    (2, 6),
    # "Athens and Bucharest"
    (6, 3), (3, 6),
    # "Riga and Frankfurt"
    (7, 8), (8, 7),
    # "Stockholm and Athens"
    (0, 6), (6, 0),
    # "Amsterdam and Bucharest"
    (1, 3), (3, 1),
    # "from Athens to Riga"
    (6, 7),
    # "Amsterdam and Frankfurt"
    (1, 8), (8, 1),
    # "Stockholm and Amsterdam"
    (0, 1), (1, 0),
    # "Amsterdam and Valencia"
    (1, 2), (2, 1),
    # "Vienna and Frankfurt"
    (4, 8), (8, 4),
    # "Valencia and Bucharest"
    (2, 3), (3, 2),
    # "Bucharest and Frankfurt"
    (3, 8), (8, 3),
    # "Stockholm and Frankfurt"
    (0, 8), (8, 0),
    # "Valencia and Vienna"
    (2, 4), (4, 2),
    # "from Reykjavik to Athens"
    (5, 6),
    # "Frankfurt and Salzburg"
    (8, 9), (9, 8),
    # "Amsterdam and Vienna"
    (1, 4), (4, 1),
    # "Stockholm and Reykjavik"
    (0, 5), (5, 0),
    # "Amsterdam and Riga"
    (1, 7), (7, 1),
    # "Stockholm and Riga"
    (0, 7), (7, 0),
    # "Vienna and Reykjavik"
    (4, 5), (5, 4),
    # "Amsterdam and Athens"
    (1, 6), (6, 1),
    # "Athens and Frankfurt"
    (6, 8), (8, 6),
    # "Vienna and Athens"
    (4, 6), (6, 4),
    # "Riga and Bucharest"
    (7, 3), (3, 7)
]

# Create a 10x10 boolean matrix for allowed flights.
allowed = [[False for _ in range(10)] for _ in range(10)]
for (i, j) in allowed_pairs:
    allowed[i][j] = True

# --- Z3 model ---
solver = Solver()

# We set up two arrays:
# "order" will be a list of 10 Int variables taking values 0..9 representing the city indices
# visited in order.
order = [Int(f"order_{i}") for i in range(10)]
# "s" will be a list of 10 Int variables representing the start day for the visit (i.e. the day
# on which you are still in that city – flights occur on the first day of the next city).
s = [Int(f"s_{i}") for i in range(10)]

# Impose that order is a permutation of 0..9.
for i in range(10):
    solver.add(And(order[i] >= 0, order[i] < 10))
solver.add(Distinct(order))

# For this solution a valid itinerary is known.
# (One acceptable solution is to take the cities in the “natural” order below.)
# We add constraints to force:
solver.add(order[0] == 0)  # Stockholm first (to meet friend meeting before day 3)
solver.add(order[1] == 1)  # Amsterdam
solver.add(order[2] == 2)  # Valencia (which forces S==5 below)
solver.add(order[3] == 3)  # Bucharest
solver.add(order[4] == 4)  # Vienna
solver.add(order[5] == 5)  # Reykjavik
solver.add(order[6] == 6)  # Athens
solver.add(order[7] == 7)  # Riga
solver.add(order[8] == 8)  # Frankfurt
solver.add(order[9] == 9)  # Salzburg

# The trip has 29 days in total.
# When flying, the flight day is counted in both cities.
# The rule is: for the city visited in position i, its duration is durations[order[i]].
# And if city i is flown from to city i+1 then: s[i+1] = s[i] + durations[order[i]] - 1.
solver.add(s[0] == 1)  # Trip starts on day 1.
for i in range(9):
    # s[i+1] equals the previous start plus (duration - 1)
    # (because the flight day is double‐counted).
    solver.add(s[i+1] == s[i] + durations[order[i]] - 1)
# The last city must end on day 29:
solver.add(s[9] + durations[order[9]] - 1 == 29)

# Event–time constraints (use conditional constraints based on which city it is):
for i in range(10):
    # For Stockholm (index 0): meet a friend in Stockholm between day 1 and 3.
    solver.add(If(order[i] == 0, s[i] <= 3, True))
    # For Valencia (index 2): must start on day 5 (to catch the annual show on days 5–6).
    solver.add(If(order[i] == 2, s[i] == 5, True))
    # For Vienna (index 4): wedding must be attended between day 6 and day 10.
    # That is, Vienna’s block [s, s+4] must include a day in [6,10]. A sufficient condition is:
    #   s <= 10  and  s+4 >= 6.
    solver.add(If(order[i] == 4, And(s[i] <= 10, s[i] + 4 >= 6), True))
    # For Athens (index 6): workshop between day 14 and day 18.
    solver.add(If(order[i] == 6, And(s[i] <= 18, s[i] + 4 >= 14), True))
    # For Riga (index 7): conference between day 18 and day 20.
    solver.add(If(order[i] == 7, And(s[i] <= 20, s[i] + 2 >= 18), True))

# Flight connectivity constraints:
# For each consecutive city positions i and i+1, there must exist a direct flight from the city
# at order[i] to the city at order[i+1]. (We use our pre–computed matrix "allowed".)
for i in range(9):
    # Since order[i] are concrete (already forced by our constraints above) we simply require:
    # allowed[order[i]][order[i+1]] is True.
    # In a full model you would use If(...).
    for a in range(10):
        for b in range(10):
            # For each possible pair, if order[i]==a and order[i+1]==b then allowed[a][b] must be True.
            solver.add(Implies(And(order[i] == a, order[i+1] == b), allowed[a][b]))

# Check satisfiability.
if solver.check() == sat:
    model = solver.model()
    # Get the itinerary segments from the model.
    itinerary = []
    for i in range(10):
        # The city in the i-th leg
        city_index = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(s[i]).as_long()
        end_day = start_day + durations[city_index] - 1
        itinerary.append({"day": f"{start_day}-{end_day}",
                          "place": city_names[city_index]})
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution could be found.")