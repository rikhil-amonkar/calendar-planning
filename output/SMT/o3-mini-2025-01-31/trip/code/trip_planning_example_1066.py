from z3 import *

# City indices and requirements:
# 0: Brussels  – 4 days.
# 1: Bucharest – 3 days.
# 2: Stuttgart – 4 days; event: meet a friend in Stuttgart between day 1 and day 4.
# 3: Mykonos  – 2 days.
# 4: Madrid   – 2 days; event: attend a conference in Madrid during day 20 and day 21.
# 5: Helsinki – 5 days.
# 6: Split    – 3 days.
# 7: London   – 5 days.
city_names = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Madrid", "Helsinki", "Split", "London"]
req = [4, 3, 4, 2, 2, 5, 3, 5]  # Total required day credits = 4+3+4+2+2+5+3+5 = 28

# Total base days = 21.
# On a day with no flight, you get 1 credit for the city.
# On a flight day (if you fly from city A to city B on that day) both cities get a credit.
# Thus, total credits = base days + (# flights) = 21 + (# flights).
# To reach 28 credits, we need exactly 7 flights.
# This partitions the trip into 8 segments (one per city).
DAYS = 21

# Allowed direct flights (bidirectional unless noted otherwise):
# 1. Helsinki and London          -> (Helsinki, London): (5,7) and (London, Helsinki): (7,5)
# 2. Split and Madrid             -> (Split, Madrid): (6,4) and (Madrid, Split): (4,6)
# 3. Helsinki and Madrid          -> (Helsinki, Madrid): (5,4) and (Madrid, Helsinki): (4,5)
# 4. London and Madrid            -> (London, Madrid): (7,4) and (Madrid, London): (4,7)
# 5. Brussels and London          -> (Brussels, London): (0,7) and (London, Brussels): (7,0)
# 6. Bucharest and London         -> (Bucharest, London): (1,7) and (London, Bucharest): (7,1)
# 7. Brussels and Bucharest       -> (Brussels, Bucharest): (0,1) and (Bucharest, Brussels): (1,0)
# 8. Bucharest and Madrid         -> (Bucharest, Madrid): (1,4) and (Madrid, Bucharest): (4,1)
# 9. Split and Helsinki           -> (Split, Helsinki): (6,5) and (Helsinki, Split): (5,6)
# 10. Mykonos and Madrid          -> (Mykonos, Madrid): (3,4) and (Madrid, Mykonos): (4,3)
# 11. Stuttgart and London        -> (Stuttgart, London): (2,7) and (London, Stuttgart): (7,2)
# 12. Helsinki and Brussels       -> (Helsinki, Brussels): (5,0) and (Brussels, Helsinki): (0,5)
# 13. Brussels and Madrid         -> (Brussels, Madrid): (0,4) and (Madrid, Brussels): (4,0)
# 14. Split and London            -> (Split, London): (6,7) and (London, Split): (7,6)
# 15. Stuttgart and Split         -> (Stuttgart, Split): (2,6) and (Split, Stuttgart): (6,2)
# 16. London and Mykonos          -> (London, Mykonos): (7,3) and (Mykonos, London): (3,7)
allowed_flights = [
    (5,7), (7,5),
    (6,4), (4,6),
    (5,4), (4,5),
    (7,4), (4,7),
    (0,7), (7,0),
    (1,7), (7,1),
    (0,1), (1,0),
    (1,4), (4,1),
    (6,5), (5,6),
    (3,4), (4,3),
    (2,7), (7,2),
    (5,0), (0,5),
    (0,4), (4,0),
    (6,7), (7,6),
    (2,6), (6,2),
    (7,3), (3,7)
]

# Create Z3 variables:
# c[d] represents the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (for d >= 1; day 0 is the starting day with no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (either day 0 or a day with a flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's base city is one of [0,7].
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d >= 1, determine if a flight occurs and restrict transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 7 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# 5. Distinct segment constraint: the starting base city for each segment (day 0 and each flight day)
# must be unique so that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also enforce that each city is visited (i.e. appears as a segment start).
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 gives 1 credit for c[0].
# For each day d >= 1:
#   - If a flight occurs on day d, add 1 credit for both the previous day's city and current day's city.
#   - Otherwise, add 1 credit for the current city's day.
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily_contrib = []
    for d in range(1, DAYS):
        daily_contrib.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily_contrib))
    s.add(counts[city] == req[city])

# Helper function: on day d, check if the itinerary "includes" a target city.
# If a flight occurs on day d, then the day counts as being in both the previous day's city
# and the current day's city. Otherwise, it is only the city c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Meet a friend in Stuttgart (city 2) between day 1 and day 4 (i.e. indices 0..3).
stuttgart_event = [inCityOnDay(d, 2) for d in range(0, 4)]
s.add(Or(stuttgart_event))

# (b) Attend a conference in Madrid (city 4) during day 20 and day 21.
# Day 20 is index 19 and day 21 is index 20.
s.add(inCityOnDay(19, 4))
s.add(inCityOnDay(20, 4))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")