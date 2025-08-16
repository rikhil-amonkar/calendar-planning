# Solve the itinerary planning problem with Z3 and output a JSON itinerary.
# Constraints:
# - 12 total days
# - Cities: Milan, Seville, Naples
# - Direct flights only between: Milan<->Seville, Milan<->Naples
# - Spend exactly: Naples 3 days, Seville 4 days (and be in Seville on days 9-12), Milan 7 days
# - Flight day counts for BOTH origin and destination cities
# - No separate flight entries; itinerary lists one city per day

from z3 import *
import json

# City encoding
MILAN, SEVILLE, NAPLES = 0, 1, 2
city_names = {MILAN: "Milan", SEVILLE: "Seville", NAPLES: "Naples"}

n_days = 12

# Decision variables: city for each day (1-indexed for readability)
city = [Int(f"city_{d}") for d in range(1, n_days + 1)]

s = Solver()

# Domain constraints
for d in range(n_days):
    s.add(Or(city[d] == MILAN, city[d] == SEVILLE, city[d] == NAPLES))

# Show attendance: Days 9-12 must be in Seville (base city)
for d in range(9, 13):
    s.add(city[d - 1] == SEVILLE)

# Direct flights constraint: if city changes from day d-1 to d, it must be direct
def is_direct(a, b):
    return Or(
        And(a == MILAN, b == SEVILLE),
        And(a == SEVILLE, b == MILAN),
        And(a == MILAN, b == NAPLES),
        And(a == NAPLES, b == MILAN),
    )

# Track if a flight occurs on day d (for d >= 2)
flight_day_flags = []
for d in range(2, n_days + 1):
    changed = city[d - 1] != city[d - 2]
    s.add(Implies(changed, is_direct(city[d - 2], city[d - 1])))
    # Int flag 0/1 for flight day
    flag = If(changed, 1, 0)
    flight_day_flags.append(flag)

# Exactly 2 flights (so total city-days = 12 + 2 = 14 = 3 + 7 + 4)
s.add(Sum(flight_day_flags) == 2)

# City-day counting with flight-day overlap:
# total_count[c] = base_count[c] + departures_from_c
def indicator(cond):
    return If(cond, 1, 0)

base_counts = {
    MILAN: Sum([indicator(city[d] == MILAN) for d in range(n_days)]),
    SEVILLE: Sum([indicator(city[d] == SEVILLE) for d in range(n_days)]),
    NAPLES: Sum([indicator(city[d] == NAPLES) for d in range(n_days)]),
}

departures = {
    MILAN: Sum([indicator(And(city[d - 1] == MILAN, city[d] != city[d - 1])) for d in range(1, n_days)]),
    SEVILLE: Sum([indicator(And(city[d - 1] == SEVILLE, city[d] != city[d - 1])) for d in range(1, n_days)]),
    NAPLES: Sum([indicator(And(city[d - 1] == NAPLES, city[d] != city[d - 1])) for d in range(1, n_days)]),
}

total_counts = {
    MILAN: base_counts[MILAN] + departures[MILAN],
    SEVILLE: base_counts[SEVILLE] + departures[SEVILLE],
    NAPLES: base_counts[NAPLES] + departures[NAPLES],
}

# Enforce required totals
s.add(total_counts[NAPLES] == 3)
s.add(total_counts[SEVILLE] == 4)
s.add(total_counts[MILAN] == 7)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

# Build itinerary (one city per day; flight days are implicitly handled in counts)
itinerary = []
for d in range(1, n_days + 1):
    c = m[city[d - 1]].as_long()
    itinerary.append({"day": d, "city": city_names[c]})

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))