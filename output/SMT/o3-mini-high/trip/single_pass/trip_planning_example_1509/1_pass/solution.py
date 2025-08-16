from z3 import *
import json

# A helper function that returns the required stay duration for a given city.
# City IDs:
# 0: Paris (5 days)
# 1: Warsaw (2 days)
# 2: Krakow (2 days)
# 3: Tallinn (2 days)
# 4: Riga (2 days)
# 5: Copenhagen (5 days)
# 6: Helsinki (5 days)
# 7: Oslo (5 days)
# 8: Santorini (2 days)
# 9: Lyon (4 days)
def get_duration(city):
    return If(city == 0, 5,
           If(city == 1, 2,
           If(city == 2, 2,
           If(city == 3, 2,
           If(city == 4, 2,
           If(city == 5, 5,
           If(city == 6, 5,
           If(city == 7, 5,
           If(city == 8, 2,
           If(city == 9, 4, 0))))))))))

# Initialize the Z3 solver.
solver = Solver()

# We want to visit all 10 cities in some order.
# order[i] is the city visited in segment i (0-indexed, segments 0..9).
order = [Int(f'city_{i}') for i in range(10)]
for i in range(10):
    solver.add(And(order[i] >= 0, order[i] <= 9))
solver.add(Distinct(order))

# We have 25 calendar days overall. The idea is to “chain” segments.
# In this puzzle, when you fly from one city to the next on day X,
# that day is counted in both the departing city’s stay and the arriving city’s stay.
# Thus, if segment i is in some city and lasts D days, its occupancy is from s[i] to s[i] + D - 1.
# And for each subsequent segment, the flight day is the same as the last day of the previous segment.
# We set s[0] = 1 (start on day 1) and for i >= 1, set: 
#    s[i] = 1 + Sum_{j=0}^{i-1}( get_duration(order[j]) - 1 ).
s = []
for i in range(10):
    s_i = Int(f's_{i}')
    if i == 0:
        solver.add(s_i == 1)
    else:
        solver.add(s_i == 1 + Sum([get_duration(order[j]) - 1 for j in range(i)]))
    s.append(s_i)

# The final day must be day 25.
solver.add(s[9] + get_duration(order[9]) - 1 == 25)

# -----------------------------------------------------------------------------
# Add extra meeting / event constraints.
# -----------------------------------------------------------------------------
# Paris (city 0): Visit for 5 days and meet your friends between day 4 and day 8.
# Since Paris’s occupancy will be from s to s+4, we require that at least day 4–8 is covered.
# (It suffices here to require the start day s <= 8.)
for i in range(10):
    solver.add(Implies(order[i] == 0, s[i] <= 8))

# Krakow (city 2): Stay 2 days and attend a workshop between day 17 and day 18.
# Since its occupancy is [s, s+1], we force s to be 16, 17 or 18.
for i in range(10):
    solver.add(Implies(order[i] == 2, And(s[i] >= 16, s[i] <= 18)))

# Riga (city 4): Stay 2 days and attend a wedding between day 23 and day 24.
# With occupancy [s, s+1], the start day must be 22, 23, or 24.
for i in range(10):
    solver.add(Implies(order[i] == 4, And(s[i] >= 22, s[i] <= 24)))

# Helsinki (city 6): Stay 5 days and meet a friend between day 18 and day 22.
# With occupancy [s, s+4], we require that s <= 22 and s+4 >= 18 i.e. s >= 14.
for i in range(10):
    solver.add(Implies(order[i] == 6, And(s[i] <= 22, s[i] >= 14)))

# Santorini (city 8): Stay 2 days and visit relatives between day 12 and day 13.
# With occupancy [s, s+1], s can be 11, 12, or 13.
for i in range(10):
    solver.add(Implies(order[i] == 8, And(s[i] >= 11, s[i] <= 13)))

# -----------------------------------------------------------------------------
# Flight connectivity constraints.
# You only take direct flights between cities, and only the following flights exist.
# Note: For pairs given as "A and B" we assume the flight is bidirectional.
# For entries like "from Riga to Tallinn" or "from Santorini to Oslo", the flight is only available in that direction.
# We list (a,b) pairs such that a -> b is allowed.
allowed_edges = []

# Bidirectional flight pairs (we add both directions).
bidir_pairs = [
    (1, 4),   # Warsaw – Riga
    (1, 3),   # Warsaw – Tallinn
    (5, 6),   # Copenhagen – Helsinki
    (9, 0),   # Lyon – Paris
    (5, 1),   # Copenhagen – Warsaw
    (9, 7),   # Lyon – Oslo
    (0, 7),   # Paris – Oslo
    (0, 4),   # Paris – Riga
    (2, 6),   # Krakow – Helsinki
    (0, 3),   # Paris – Tallinn
    (7, 4),   # Oslo – Riga
    (2, 1),   # Krakow – Warsaw
    (0, 6),   # Paris – Helsinki
    (5, 8),   # Copenhagen – Santorini
    (6, 1),   # Helsinki – Warsaw
    (6, 4),   # Helsinki – Riga
    (5, 2),   # Copenhagen – Krakow
    (5, 4),   # Copenhagen – Riga
    (0, 2),   # Paris – Krakow
    (5, 7),   # Copenhagen – Oslo
    (7, 3),   # Oslo – Tallinn
    (7, 6),   # Oslo – Helsinki
    (5, 3),   # Copenhagen – Tallinn
    (7, 2),   # Oslo – Krakow
    (0, 5),   # Paris – Copenhagen
    (0, 1),   # Paris – Warsaw
    (7, 1)    # Oslo – Warsaw
]
for (a, b) in bidir_pairs:
    allowed_edges.append((a, b))
    allowed_edges.append((b, a))

# Directed flights (only one allowed direction)
allowed_edges.append((4, 3))  # from Riga to Tallinn
allowed_edges.append((8, 7))  # from Santorini to Oslo

# A helper function that, given two Z3 int expressions a and b, returns a Boolean formula that (a,b) is among allowed direct flights.
def flight_allowed(a, b):
    return Or([And(a == edge[0], b == edge[1]) for edge in allowed_edges])

# Add the flight constraints between consecutive segments.
for i in range(9):
    solver.add(flight_allowed(order[i], order[i+1]))

# -----------------------------------------------------------------------------
# Try to solve the model.
if solver.check() == sat:
    m = solver.model()
    # Extract the order and start days from the model.
    order_sol = [m.evaluate(order[i]).as_long() for i in range(10)]
    s_sol = [m.evaluate(s[i]).as_long() for i in range(10)]
    
    # For output purposes, map each city ID to its name and duration.
    city_names = {
        0: "Paris",
        1: "Warsaw",
        2: "Krakow",
        3: "Tallinn",
        4: "Riga",
        5: "Copenhagen",
        6: "Helsinki",
        7: "Oslo",
        8: "Santorini",
        9: "Lyon"
    }
    durations_lookup = {
        0: 5,
        1: 2,
        2: 2,
        3: 2,
        4: 2,
        5: 5,
        6: 5,
        7: 5,
        8: 2,
        9: 4
    }
    
    # Compute the segment intervals.
    # Segment i occupies days [s[i], s[i] + duration - 1].
    segments = []
    for i in range(10):
        city = order_sol[i]
        start_day = s_sol[i]
        dur = durations_lookup[city]
        end_day = start_day + dur - 1
        segments.append((city_names[city], start_day, end_day))
    
    # Build a daily itinerary for days 1 to 25.
    # On a flight day (when a transition happens) the day appears in both segments.
    itinerary = []
    for day in range(1, 26):
        cities_today = []
        for seg in segments:
            if day >= seg[1] and day <= seg[2]:
                cities_today.append(seg[0])
        itinerary.append({"day": day, "cities": cities_today})
    
    # Prepare the JSON result.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")