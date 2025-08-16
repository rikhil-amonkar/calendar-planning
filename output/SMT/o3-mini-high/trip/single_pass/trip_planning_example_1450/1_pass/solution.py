from z3 import *
import json

# List of cities (by index) with their fixed durations.
# Indices:
# 0: Stockholm (3 days)
# 1: Hamburg (5 days)
# 2: Florence (2 days)
# 3: Istanbul (5 days) [and must cover days 25–29]
# 4: Oslo (5 days)
# 5: Vilnius (5 days)
# 6: Santorini (2 days)
# 7: Munich (5 days)
# 8: Frankfurt (4 days)
# 9: Krakow (5 days) [workshop must be attended between day 5 and day 9]
cities = {
    0: "Stockholm",
    1: "Hamburg",
    2: "Florence",
    3: "Istanbul",
    4: "Oslo",
    5: "Vilnius",
    6: "Santorini",
    7: "Munich",
    8: "Frankfurt",
    9: "Krakow"
}

# durations corresponding to each city (by index)
durations = {
    0: 3,  # Stockholm
    1: 5,  # Hamburg
    2: 2,  # Florence
    3: 5,  # Istanbul
    4: 5,  # Oslo
    5: 5,  # Vilnius
    6: 2,  # Santorini
    7: 5,  # Munich
    8: 4,  # Frankfurt
    9: 5   # Krakow
}

# Allowed flight connections.
# Note: Whenever the flight is given with “and” we treat it bidirectional.
# When given as "from X to Y", then the move is one-directional.
allowed_moves = [
    # Bidirectional flights:
    (4, 0), (0, 4),       # Oslo <-> Stockholm
    (9, 8), (8, 9),       # Krakow <-> Frankfurt
    (9, 3), (3, 9),       # Krakow <-> Istanbul
    (7, 0), (0, 7),       # Munich <-> Stockholm
    (1, 0), (0, 1),       # Hamburg <-> Stockholm
    (4, 3), (3, 4),       # Oslo <-> Istanbul
    (3, 0), (0, 3),       # Istanbul <-> Stockholm
    (4, 5), (5, 4),       # Oslo <-> Vilnius
    (5, 3), (3, 5),       # Vilnius <-> Istanbul
    (8, 3), (3, 8),       # Frankfurt <-> Istanbul
    (4, 8), (8, 4),       # Oslo <-> Frankfurt
    (7, 1), (1, 7),       # Munich <-> Hamburg
    (7, 3), (3, 7),       # Munich <-> Istanbul
    (4, 7), (7, 4),       # Oslo <-> Munich
    (8, 2), (2, 8),       # Frankfurt <-> Florence
    (4, 1), (1, 4),       # Oslo <-> Hamburg
    (5, 8), (8, 5),       # Vilnius <-> Frankfurt
    (9, 7), (7, 9),       # Krakow <-> Munich
    (1, 3), (3, 1),       # Hamburg <-> Istanbul
    (8, 0), (0, 8),       # Frankfurt <-> Stockholm
    (8, 7), (7, 8),       # Frankfurt <-> Munich
    (9, 0), (0, 9),       # Krakow <-> Stockholm
    (8, 1), (1, 8),       # Frankfurt <-> Hamburg

    # Directed edges:
    (9, 5),    # from Krakow to Vilnius (only allowed in this direction)
    (2, 7),    # from Florence to Munich (only allowed in this direction)
    (0, 6),    # from Stockholm to Santorini (only allowed in this direction)
    (6, 4),    # from Santorini to Oslo (only allowed in this direction)
    (5, 7)     # from Vilnius to Munich (only allowed in this direction)
]

# Helper: given a z3 expression representing a city (int), return its duration.
def get_duration(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4],
           If(city_var == 5, durations[5],
           If(city_var == 6, durations[6],
           If(city_var == 7, durations[7],
           If(city_var == 8, durations[8],
           If(city_var == 9, durations[9],
           -1)))))))))


# Create variables:
# order[i] is an integer variable from 0 to 9 representing which city is visited in segment i.
# There are 10 segments (one per city); the overall timeline is determined by overlapping flight days.
num_segments = 10
order = [Int(f"order_{i}") for i in range(num_segments)]
# s[i] is the starting day for segment i.
s = [Int(f"s_{i}") for i in range(num_segments)]

solver = Solver()

# Each order must be an integer between 0 and 9.
for i in range(num_segments):
    solver.add(And(order[i] >= 0, order[i] <= 9))
    
# All cities are visited exactly once.
solver.add(Distinct(order))

# First segment starts on day 1.
solver.add(s[0] == 1)

# The recurrence between segments:
# When you fly from city A to city B on the flight day (which is the starting day of B),
# that day counts for both A and B. Hence, if city A (with duration d) is visited starting on s,
# its “stay” covers days s through (s + d - 1) and then s_next must equal (s + d - 1).
for i in range(num_segments - 1):
    solver.add(s[i+1] == s[i] + get_duration(order[i]) - 1)
    
# The overall timeline has 32 days.
solver.add(s[num_segments - 1] + get_duration(order[num_segments - 1]) - 1 == 32)

# Special constraint: Istanbul (city index 3) must be visited so that its segment covers days 25-29.
# Since its duration is 5, the only way is to have its segment exactly on days 25–29.
for i in range(num_segments):
    solver.add(Implies(order[i] == 3, s[i] == 25))

# Special constraint: Krakow (city index 9) must include the workshop between day 5 and day 9.
# Krakow has 5 days. For the interval [s, s+4] to intersect [5,9], it is sufficient that s <= 9.
for i in range(num_segments):
    solver.add(Implies(order[i] == 9, s[i] <= 9))

# Flight connectivity constraint:
# For each transition between consecutive segments, the flight from the city in the current segment
# to the city in the next segment must be allowed (using only direct flights).
for i in range(num_segments - 1):
    allowed_exprs = []
    for (a, b) in allowed_moves:
        allowed_exprs.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(allowed_exprs))

# Solve!
if solver.check() == sat:
    model = solver.model()
    itinerary_segments = []
    # Build a list of segments: each with a start day, end day, and city name.
    for i in range(num_segments):
        city_idx = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(s[i]).as_long()
        dur = durations[city_idx]
        end_day = start_day + dur - 1
        itinerary_segments.append({
            "start_day": start_day,
            "end_day": end_day,
            "city": cities[city_idx]
        })
        
    # For clarity, sort segments by start_day (they are already in order because of our recurrence)
    itinerary_segments = sorted(itinerary_segments, key=lambda x: x["start_day"])
    
    result = {"itinerary": itinerary_segments}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")