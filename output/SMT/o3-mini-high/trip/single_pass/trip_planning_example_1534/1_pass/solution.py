from z3 import *
import json

# The fixed ordering of cities (one valid Hamiltonian path using only direct flights):
cities = [
    "Paris",      # Workshop takes place between day 1 and 2.
    "Barcelona",  # Meet your friends between day 2 and day 6.
    "Florence",
    "Amsterdam",
    "Tallinn",    # Meet a friend here between day 11 and 12.
    "Vilnius",
    "Warsaw",
    "Venice",
    "Hamburg",    # Conference: must be in Hamburg from day 19 to day 22.
    "Salzburg"    # Wedding: attend between day 22 and day 25.
]

# Planned durations (in days) for each city.
durations = {
    "Paris": 2,
    "Barcelona": 5,
    "Florence": 5,
    "Amsterdam": 2,
    "Tallinn": 2,
    "Vilnius": 3,
    "Warsaw": 4,
    "Venice": 3,
    "Hamburg": 4,
    "Salzburg": 4
}

n = len(cities)
# s[i] is the start day in city i (its “arrival” or flight day)
s = [Int(f"s_{i}") for i in range(n)]
solver = Solver()

# The trip starts on day 1.
solver.add(s[0] == 1)

# For each consecutive pair, if you fly from city i to city i+1 on a day X then X must lie 
# in the interval in city i. (On day X you are counted as being in both cities.)
for i in range(n-1):
    d = durations[cities[i]]
    # Flight day constraint: s[i+1] must be between s[i] and s[i] + d - 1.
    solver.add(s[i+1] >= s[i])
    solver.add(s[i+1] <= s[i] + d - 1)

# The entire itinerary ends exactly when the last city’s stay finishes.
# That is, final day = s[last] + duration(last) - 1 = 25.
solver.add(s[n-1] + durations[cities[n-1]] - 1 == 25)

# ---------------------------
# Special Time Constraints:
# (1) Workshop in Paris (index 0): Paris’s interval is [s0, s0+1] = [1,2]. (Automatically okay.)

# (2) Friends meeting in Barcelona (index 1):
# Barcelona’s stay is from s[1] to s[1]+5-1. To ensure this interval overlaps with [2,6],
# we can require that the start day is no later than 6.
solver.add(s[1] <= 6)

# (3) Meeting a friend in Tallinn (index 4):
# Tallinn’s interval is [s[4], s[4]+1]. We require that some day in {11,12} is covered.
solver.add(s[4] >= 10)  # so that s[4]+1 >= 11
solver.add(s[4] <= 12)

# (4) Hamburg conference (index 8):
# Hamburg’s stay must be exactly day 19–22 so we set its start day of Hamburg to 19.
solver.add(s[8] == 19)

# (5) Salzburg wedding (index 9):
# We fly from Hamburg to Salzburg on a day that counts for both.
# For the wedding the Salzburg interval must include a day in [22,25];
# by forcing s[9] = 22 (so that Salzburg covers 22–25) this is satisfied.
solver.add(s[9] == 22)

# ---------------------------
# Solve!
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i, city in enumerate(cities):
        start_day = model[s[i]].as_long()
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "city": city,
            "start_day": start_day,
            "end_day": end_day
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")