# Solve the trip planning problem with Z3 and output a JSON itinerary.
# Rules:
# - 12 total days, cities: Brussels, Barcelona, Split
# - Only direct flights: Brussels<->Barcelona, Barcelona<->Split
# - Flight day counts for BOTH origin and destination cities
# - Spend exactly: Brussels 2 days (and be in Brussels on Day 1 and Day 2), Barcelona 7 days, Split 5 days
# - JSON output: {"itinerary": [{"day": i, "city": name}, ...]}

from z3 import *
import json

# Constants
DAYS = 12
BRUSSELS, BARCELONA, SPLIT = 0, 1, 2
CITY_NAMES = {BRUSSELS: "Brussels", BARCELONA: "Barcelona", SPLIT: "Split"}

# Allowed direct flights (undirected)
ALLOWED = {(BRUSSELS, BARCELONA), (BARCELONA, BRUSSELS), (BARCELONA, SPLIT), (SPLIT, BARCELONA)}

# Z3 variables
day_city = [Int(f"city_{d+1}") for d in range(DAYS)]

s = Solver()

# Domain constraints for each day: one of the three cities
for d in range(DAYS):
    s.add(Or(day_city[d] == BRUSSELS, day_city[d] == BARCELONA, day_city[d] == SPLIT))

# Only direct flights when changing cities
for d in range(1, DAYS):
    s.add(Implies(day_city[d] != day_city[d-1],
                  Or([And(day_city[d-1] == a, day_city[d] == b) for (a, b) in ALLOWED])))

# Define inCity[c][d]: you are "in" city c on day d if:
# - the assigned city for day d is c, OR
# - day d is a flight day (city changes from day d-1 to d) and day d-1 was c (so both count day d)
inCity = [[Bool(f"in_{c}_{d+1}") for d in range(DAYS)] for c in (BRUSSELS, BARCELONA, SPLIT)]

for d in range(DAYS):
    for c in (BRUSSELS, BARCELONA, SPLIT):
        if d == 0:
            s.add(inCity[c][d] == (day_city[d] == c))
        else:
            s.add(inCity[c][d] == Or(day_city[d] == c,
                                     And(day_city[d-1] == c, day_city[d] != day_city[d-1])))

# City day count constraints (counting flight days for both sides)
def count_days(c):
    return Sum([If(inCity[c][d], 1, 0) for d in range(DAYS)])

s.add(count_days(BRUSSELS) == 2)
s.add(count_days(BARCELONA) == 7)
s.add(count_days(SPLIT) == 5)

# Conference in Brussels on Day 1 and Day 2 (must be in Brussels on those days)
s.add(inCity[BRUSSELS][0] == True)  # Day 1
s.add(inCity[BRUSSELS][1] == True)  # Day 2

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

# Build itinerary: assign a single city per day (no separate flight entries).
itinerary = []
for d in range(DAYS):
    city_val = m[day_city[d]].as_long()
    itinerary.append({"day": d + 1, "city": CITY_NAMES[city_val]})

# Output JSON
print(json.dumps({"itinerary": itinerary}, indent=2))