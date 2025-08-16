# Solve the trip planning problem with Z3 and output a JSON itinerary.
# Constraints:
# - 5 cities: Geneva (GVA), Munich (MUC), Valencia (VLC), Bucharest (BUH), Stuttgart (STR)
# - Total timeline: 17 days (days are 1..17)
# - Stays:
#    Geneva: 4 days, and within days 1..4 (we'll fix days 1..4 to Geneva)
#    Munich: 7 days
#    Valencia: 6 days
#    Bucharest: 2 days
#    Stuttgart: 2 days
# - Direct flights only between consecutive days:
#    GVA-MUC, MUC-VLC, BUH-VLC, MUC-BUH, VLC-STR, GVA-VLC (undirected)
# - Being on a flight on day d from A to B means day d counts for both A and B.
#   We model this by:
#   count(city C) = occurrences of C on days + number of arrivals into C (i.e., d where city[d+1] == C and city[d] != C)
# - Meet friends in Munich between day 4 and day 10 inclusive (present in MUC on at least one of those days).
# - Output: JSON with 'itinerary': [{ "day": i, "place": CityName }, ...]
#
# The solver will find a valid itinerary and we print the day-place mapping
# (no separate flight entries; flight counting is handled in constraints).

from z3 import Solver, Int, If, And, Or, Sum, sat
import json

# Cities and mapping
cities = ["Geneva", "Munich", "Valencia", "Bucharest", "Stuttgart"]
GVA, MUC, VLC, BUH, STR = range(5)

# Allowed undirected direct-flight edges (as pairs of ints)
edges = {
    (GVA, MUC), (MUC, GVA),
    (MUC, VLC), (VLC, MUC),
    (BUH, VLC), (VLC, BUH),
    (MUC, BUH), (BUH, MUC),
    (VLC, STR), (STR, VLC),
    (GVA, VLC), (VLC, GVA),
}

days = 17
# city_on_day[d] in {0..4} indicates the main city listed for that day d (1-based index in logic, 0-based in list)
city_on_day = [Int(f"city_{d}") for d in range(1, days + 1)]

s = Solver()

# Domain constraints
for var in city_on_day:
    s.add(var >= 0, var < 5)

# Geneva between day 1 and day 4 exclusively; fix days 1..4 to Geneva and forbid Geneva afterward
for d in range(1, 5):
    s.add(city_on_day[d - 1] == GVA)
for d in range(5, days + 1):
    s.add(city_on_day[d - 1] != GVA)

# Transition constraints: stay or direct flight
for d in range(1, days):  # transitions from day d to day d+1
    a = city_on_day[d - 1]
    b = city_on_day[d]
    s.add(Or(a == b, Or(*[And(a == x, b == y) for (x, y) in edges])))

def b2i(cond):
    return If(cond, 1, 0)

# Count days per city with flight-day double counting for arrival cities
counts = {}
for c in [GVA, MUC, VLC, BUH, STR]:
    base = Sum([b2i(city_on_day[d] == c) for d in range(days)])
    arrivals = Sum([b2i(And(city_on_day[d + 1] == c, city_on_day[d] != city_on_day[d + 1])) for d in range(days - 1)])
    counts[c] = base + arrivals

# Required totals
s.add(counts[GVA] == 4)
s.add(counts[MUC] == 7)
s.add(counts[VLC] == 6)
s.add(counts[BUH] == 2)
s.add(counts[STR] == 2)

# Ensure presence in Munich between day 4 and day 10 inclusive
present_muc_any = []
for d in range(4, 11):
    # Present if listed in MUC on day d, or if day d is an arrival day into MUC (i.e., city_{d+1} == MUC and city_d != city_{d+1})
    cond = Or(
        city_on_day[d - 1] == MUC,
        And(
            d <= 16,  # arrival day defined only for d <= 16
            city_on_day[d] == MUC,
            city_on_day[d - 1] != city_on_day[d]
        )
    )
    present_muc_any.append(cond)
s.add(Or(*present_muc_any))

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under given constraints.")

m = s.model()
itinerary = []
for d in range(1, days + 1):
    c = m[city_on_day[d - 1]].as_long()
    itinerary.append({"day": d, "place": cities[c]})

print(json.dumps({"itinerary": itinerary}, indent=2))