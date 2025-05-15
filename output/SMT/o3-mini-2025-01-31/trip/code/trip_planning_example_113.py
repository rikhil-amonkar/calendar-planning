from z3 import *

# City indices and requirements:
# 0: Naples   – required 3 days.
# 1: Seville  – required 4 days; event: attend annual show in Seville from day 9 to day 12.
# 2: Milan    – required 7 days.
city_names = ["Naples", "Seville", "Milan"]
required_credits = [3, 4, 7]
# Total required credits = 3 + 4 + 7 = 14

# Total itinerary days:
DAYS = 12
# The credit rule: each non-flight day yields 1 credit for that day's city,
# while a flight day (where you change the city) yields 1 credit for the departure and 1 credit for the arrival.
# So total credits = DAYS + (# flight-days)
# We need: DAYS + (# flights) = 14  -> # flights = 14 - 12 = 2.
REQUIRED_FLIGHTS = 2

# Allowed direct flights:
# Milan and Seville: (2,1) and (1,2)
# Naples and Milan:   (0,2) and (2,0)
allowed_flights = [
    (2, 1), (1, 2),
    (0, 2), (2, 0)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] is the city index on day d (for d = 0, 1, ..., DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates if a flight occurs on day d.
# Convention: day 0 is not a flight day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be one of our cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, set flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes compared to the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day, both the departure (of day d) and the arrival (of day d) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city:
# - Day 0 yields 1 credit for c[0].
# - For day d >= 1:
#     if no flight: 1 credit for c[d]
#     if flight: 1 credit for departure (c[d-1]) and 1 credit for arrival (c[d])
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
    # Enforce the required credit (day count) per city.
    s.add(counts[city] == required_credits[city])
    # Also, ensure that each city appears at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))
    
# Event constraints:
# Annual show in Seville (city 1) from day 9 to day 12.
# Days 9 to 12 correspond to indices 8, 9, 10, 11.
for d in range(8, 12):
    s.add(inCityOnDay(d, 1))
    
# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")