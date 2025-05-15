from z3 import *

# City indices:
# 0: Mykonos    – required 4 days; event: visit relatives in Mykonos between day 15 and day 18.
# 1: Krakow     – required 5 days.
# 2: Vilnius    – required 2 days.
# 3: Helsinki   – required 2 days.
# 4: Dubrovnik  – required 3 days; event: annual show in Dubrovnik from day 2 to day 4.
# 5: Oslo       – required 2 days; event: meet your friends at Oslo between day 1 and day 2.
# 6: Madrid     – required 5 days.
# 7: Paris      – required 2 days.
city_names = ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"]
required_credits = [4, 5, 2, 2, 3, 2, 5, 2]
# Total required credits = 4+5+2+2+3+2+5+2 = 25

# Total itinerary days:
DAYS = 18
# Credit rule:
#   - If a day has no flight then it contributes 1 credit for the city on that day.
#   - If a day includes a flight (city change) then it contributes 1 credit for the departure city and 1 for the arrival city.
# Thus, total credits = DAYS + (# flight-days). We need 25 credits.
# So (# flight-days) must equal 25 - 18 = 7.
REQUIRED_FLIGHTS = 7

# Allowed direct flights (bidirectional unless noted otherwise)
# Mapping cities to indices:
# Oslo and Krakow:         (5,1) and (1,5)
# Oslo and Paris:          (5,7) and (7,5)
# Paris and Madrid:        (7,6) and (6,7)
# Helsinki and Vilnius:    (3,2) and (2,3)
# Oslo and Madrid:         (5,6) and (6,5)
# Oslo and Helsinki:       (5,3) and (3,5)
# Helsinki and Krakow:     (3,1) and (1,3)
# Dubrovnik and Helsinki:  (4,3) and (3,4)
# Dubrovnik and Madrid:    (4,6) and (6,4)
# Oslo and Dubrovnik:      (5,4) and (4,5)
# Krakow and Paris:        (1,7) and (7,1)
# Madrid and Mykonos:      (6,0) and (0,6)
# Oslo and Vilnius:        (5,2) and (2,5)
# from Krakow to Vilnius:  one-way: (1,2)
# Helsinki and Paris:      (3,7) and (7,3)
# Vilnius and Paris:       (2,7) and (7,2)
# Helsinki and Madrid:     (3,6) and (6,3)
allowed_flights = [
    (5,1), (1,5),
    (5,7), (7,5),
    (7,6), (6,7),
    (3,2), (2,3),
    (5,6), (6,5),
    (5,3), (3,5),
    (3,1), (1,3),
    (4,3), (3,4),
    (4,6), (6,4),
    (5,4), (4,5),
    (1,7), (7,1),
    (6,0), (0,6),
    (5,2), (2,5),
    (1,2),         # one-way from Krakow to Vilnius
    (3,7), (7,3),
    (2,7), (7,2),
    (3,6), (6,3)
]

s = Solver()

# Variables:
# c[d]: city on day d (d=0,...,DAYS-1). Domain: 0..7.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: boolean indicator that a flight (city change) occurs on day d.
# Convention: day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints for cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1..DAYS-1, set the flight indicator and ensure allowed transitions on flight days.
for d in range(1, DAYS):
    # Flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight happens, then (c[d-1] -> c[d]) must be in allowed_flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns an expression that's true if on day d the itinerary "includes" target city.
# Note: on a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for city c[0]. For d>=1:
#    - If no flight on day d then add 1 credit to c[d].
#    - If a flight happens then add 1 credit to both c[d-1] and c[d].
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily))
    # Enforce that the computed day credits equal the required number.
    s.add(counts[city] == required_credits[city])
    # Additionally, ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Annual show in Dubrovnik from day 2 to day 4.
# That is, at least on one day among day 2,3,4 (indices 1, 2, 3) the itinerary includes Dubrovnik (city 4).
s.add(Or([inCityOnDay(d, 4) for d in [1, 2, 3]]))

# 2. Meet your friends at Oslo between day 1 and day 2.
# That is, at least on one day among day 1,2 (indices 0 and 1) the itinerary includes Oslo (city 5).
s.add(Or(inCityOnDay(0, 5), inCityOnDay(1, 5)))

# 3. Visit relatives in Mykonos between day 15 and day 18.
# That is, at least on one day among day 15-18 (indices 14,15,16,17) the itinerary includes Mykonos (city 0).
s.add(Or([inCityOnDay(d, 0) for d in [14, 15, 16, 17]]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_str += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")