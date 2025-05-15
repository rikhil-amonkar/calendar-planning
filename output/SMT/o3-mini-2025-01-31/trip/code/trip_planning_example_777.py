from z3 import *

# City indices and day credit requirements:
# 0: Dublin    – required 5 days.
# 1: Helsinki  – required 3 days; event: meet friends in Helsinki between day 3 and day 5.
# 2: Riga      – required 3 days.
# 3: Reykjavik – required 2 days.
# 4: Vienna    – required 2 days; event: annual show in Vienna from day 2 to day 3.
# 5: Tallinn   – required 5 days; event: wedding in Tallinn between day 7 and day 11.
city_names = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
required_credits = [5, 3, 3, 2, 2, 5]
# Total required credits = 5 + 3 + 3 + 2 + 2 + 5 = 20

# Total itinerary days:
DAYS = 15
# Credit rule:
#   Each day with no flight contributes 1 credit for that day's city.
#   On a flight day (when you change cities) you get 1 credit for the departure and 1 for the arrival.
# Hence, total credits = DAYS + (# flight-days).
# We need 20 credits so (# flight-days) must be 20 - 15 = 5.
REQUIRED_FLIGHTS = 5

# Allowed direct flights:
# • Helsinki and Riga            : (1,2) and (2,1)
# • from Riga to Tallinn         : (2,5)  (unidirectional)
# • Vienna and Helsinki          : (4,1) and (1,4)
# • Riga and Dublin              : (2,0) and (0,2)
# • Vienna and Riga              : (4,2) and (2,4)
# • Reykjavik and Vienna         : (3,4) and (4,3)
# • Reykjavik and Helsinki       : (3,1) and (1,3)
# • Reykjavik and Dublin         : (3,0) and (0,3)
# • Helsinki and Tallinn         : (1,5) and (5,1)
# • Vienna and Dublin            : (4,0) and (0,4)
allowed_flights = [
    (1,2), (2,1),
    (2,5),  # unidirectional from Riga to Tallinn 
    (4,1), (1,4),
    (2,0), (0,2),
    (4,2), (2,4),
    (3,4), (4,3),
    (3,1), (1,3),
    (3,0), (0,3),
    (1,5), (5,1),
    (4,0), (0,4)
]

# Create the Z3 solver
s = Solver()

# Variables:
# c[d] represents the city visited on day d (for d = 0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating if a flight (city change) occurs on day d.
# Convention: No flight on day 0.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day, the city index must be between 0 and 5.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
    
s.add(flight[0] == False)

# Transition constraints:
# For day d >= 1, a flight occurs if c[d] != c[d-1]. If a flight occurs, the city transition must be allowed.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper: inCityOnDay(d, target)
# Returns a condition that's true if on day d the target city is "covered".
# On a flight day, both the departure (previous city) and arrival (current city) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Calculate the day credits for each city.
# Day 0 gives 1 credit to the city c[0].
# For day d>=1:
#   - if no flight on day d, add 1 credit for city c[d].
#   - if flight on day d, add 1 credit for c[d-1] and 1 credit for c[d].
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
    # Enforce required credits for each city.
    s.add(counts[city] == required_credits[city])
    # Also ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Meet friends in Helsinki (city index 1) between day 3 and day 5.
# Days 3 to 5 are indices 2, 3, and 4.
s.add(Or([inCityOnDay(d, 1) for d in range(2, 5)]))

# 2. Annual show in Vienna (city index 4) from day 2 to day 3.
# Day 2 is index 1 and day 3 is index 2. We'll require both days.
s.add(inCityOnDay(1, 4))
s.add(inCityOnDay(2, 4))

# 3. Wedding in Tallinn (city index 5) between day 7 and day 11.
# Days 7 to 11 correspond to indices 6, 7, 8, 9, 10.
s.add(Or([inCityOnDay(d, 5) for d in range(6, 11)]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")