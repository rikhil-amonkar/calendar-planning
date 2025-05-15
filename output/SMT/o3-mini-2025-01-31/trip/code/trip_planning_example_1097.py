from z3 import *

# Cities (index and name):
# 0: Reykjavik (4 days)
# 1: Riga (2 days; friend meeting between day 4 and 5)
# 2: Oslo (3 days)
# 3: Lyon (5 days)
# 4: Dubrovnik (2 days; wedding between day 7 and 8)
# 5: Madrid (2 days)
# 6: Warsaw (4 days)
# 7: London (3 days)
city_names = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]

# Required day counts for each city:
req = [4, 2, 3, 5, 2, 2, 4, 3]

# Allowed direct flights.
# Note: most pairs are bidirectional except "from Reykjavik to Madrid" which is one–direction only.
allowed_flights = [
    # Warsaw and Reykjavik
    (6, 0), (0, 6),
    # Oslo and Madrid
    (2, 5), (5, 2),
    # Warsaw and Riga
    (6, 1), (1, 6),
    # Lyon and London
    (3, 7), (7, 3),
    # Madrid and London
    (5, 7), (7, 5),
    # Warsaw and London
    (6, 7), (7, 6),
    # from Reykjavik to Madrid (only this direction)
    (0, 5),
    # Warsaw and Oslo
    (6, 2), (2, 6),
    # Oslo and Dubrovnik
    (2, 4), (4, 2),
    # Oslo and Reykjavik
    (2, 0), (0, 2),
    # Riga and Oslo
    (1, 2), (2, 1),
    # Oslo and Lyon
    (2, 3), (3, 2),
    # Oslo and London
    (2, 7), (7, 2),
    # London and Reykjavik
    (7, 0), (0, 7),
    # Warsaw and Madrid
    (6, 5), (5, 6),
    # Madrid and Lyon
    (5, 3), (3, 5),
    # Dubrovnik and Madrid
    (4, 5), (5, 4)
]

# Total itinerary days.
DAYS = 18

# The required total day contributions equals sum(req)=4+2+3+5+2+2+4+3 = 25.
# With 18 base days and extra counts on flight days, we have:
#    total contributions = 18 + (#flights).
# Thus, #flights must be: 18 + f = 25  =>  f = 7.
# So we must have exactly 7 flight days (and so 8 segments for 8 different cities).

# Create Z3 variables.
# c[d] will be the base city on day d (0-indexed, i.e. day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating if on day d (d >= 1) a flight occurs such that c[d] != c[d-1].
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 is always a segment start, and any day with a flight is a segment start).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of the 8.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 8))

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicator and require allowed flights.
for d in range(1, DAYS):
    # flight occurs if the city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the pair (c[d-1], c[d]) must be in the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 7 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# The cities at the start of each segment must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, ensure that each city appears at least once.
for city in range(8):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute "day contribution" counts.
# On day 0, the traveler contributes 1 to the city c[0].
# For day d (d>=1): if there's no flight, only c[d] gets 1;
# if there is a flight, both c[d-1] and c[d] get 1.
counts = [Int(f"count_{city}") for city in range(8)]
for city in range(8):
    day0_contrib = If(c[0] == city, 1, 0)
    daily_contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        daily_contribs.append(contrib)
    s.add(counts[city] == day0_contrib + Sum(daily_contribs))
    s.add(counts[city] == req[city])

# Helper function: for a given day d, the traveler "includes" a target city.
# On day 0, it's simply c[0] == target.
# For d>=1, if a flight occurs then the traveler is in c[d-1] and c[d] (both count),
# else just in c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:
# 1. Meet a friend in Riga (city 1) between day 4 and day 5.
#    That is, at least one day among day4 and day5 (indices 3 and 4) is in Riga.
friend_riga = [inCityOnDay(d, 1) for d in range(3, 5)]
s.add(Or(friend_riga))

# 2. Attend a wedding in Dubrovnik (city 4) between day 7 and day 8.
#    That is, at least one day among day7 and day8 (indices 6 and 7) is in Dubrovnik.
wedding_dubrovnik = [inCityOnDay(d, 4) for d in range(6, 8)]
s.add(Or(wedding_dubrovnik))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        day_str = f"Day {d+1:2d}: In {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            day_str += f" (Flight: {city_names[m[c[d-1]].as_long()]} -> {city_names[m[c[d]].as_long()]})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(8):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")