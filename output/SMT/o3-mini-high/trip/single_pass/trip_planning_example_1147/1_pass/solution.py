from z3 import *
import json

# We use the following indices for the cities:
# 0: Brussels (3 days)
# 1: Helsinki (3 days)
# 2: Split (4 days)
# 3: Dubrovnik (2 days)
# 4: Istanbul (5 days) [Also: annual show from day 1 to 5 must be here]
# 5: Milan (4 days)
# 6: Vilnius (5 days) [Also: workshop must be attended in Vilnius between day 18 and 22]
# 7: Frankfurt (3 days) [Also: wedding in Frankfurt between day 16 and 18]

# Duration for each city (by index)
durations = [3, 3, 4, 2, 5, 4, 5, 3]

# Allowed flight legs as (from, to).
# All pairs marked "and" are bidirectional.
# There are two directed exceptions:
#   - Flight from Dubrovnik (3) to Istanbul (4) is allowed (but not the reverse).
#   - Flight from Brussels (0) to Frankfurt (7) is allowed (but not the reverse).
allowed_pairs = [
    (5, 7), (7, 5),              # Milan <-> Frankfurt
    (2, 7), (7, 2),              # Split <-> Frankfurt
    (5, 2), (2, 5),              # Milan <-> Split
    (0, 6), (6, 0),              # Brussels <-> Vilnius
    (0, 1), (1, 0),              # Brussels <-> Helsinki
    (4, 0), (0, 4),              # Istanbul <-> Brussels
    (5, 6), (6, 5),              # Milan <-> Vilnius
    (0, 5), (5, 0),              # Brussels <-> Milan
    (4, 1), (1, 4),              # Istanbul <-> Helsinki
    (1, 6), (6, 1),              # Helsinki <-> Vilnius
    (1, 3), (3, 1),              # Helsinki <-> Dubrovnik
    (2, 6), (6, 2),              # Split <-> Vilnius
    (4, 5), (5, 4),              # Istanbul <-> Milan
    (1, 7), (7, 1),              # Helsinki <-> Frankfurt
    (4, 6), (6, 4),              # Istanbul <-> Vilnius
    (2, 1), (1, 2),              # Split <-> Helsinki
    (5, 1), (1, 5),              # Milan <-> Helsinki
    (4, 7), (7, 4),              # Istanbul <-> Frankfurt
    (3, 7), (7, 3),              # Dubrovnik <-> Frankfurt
    (7, 6), (6, 7),              # Frankfurt <-> Vilnius
    # Directed flights:
    (3, 4),                     # from Dubrovnik to Istanbul only
    (0, 7)                      # from Brussels to Frankfurt only
]

# Map each city index to its name.
city_names = {
    0: "Brussels",
    1: "Helsinki",
    2: "Split",
    3: "Dubrovnik",
    4: "Istanbul",
    5: "Milan",
    6: "Vilnius",
    7: "Frankfurt"
}

# Create solver
solver = Solver()

# There will be 8 segments (one per city visit); note that flying from one city to the next happens on the last day of the segment.
N = 8

# Create an array for the itinerary ordering (each value in 0..7 with no repetition)
itinerary = [Int(f"itinerary_{i}") for i in range(N)]
for i in range(N):
    solver.add(And(itinerary[i] >= 0, itinerary[i] <= 7))
solver.add(Distinct(itinerary))

# Istanbul must be visited first (because the annual show in Istanbul is from day 1 to 5)
solver.add(itinerary[0] == 4)

# Create an array for the starting day (for each city segment)
start = [Int(f"start_{i}") for i in range(N)]
for i in range(N):
    solver.add(start[i] >= 1, start[i] <= 22)

# Istanbul segment must start at day 1.
solver.add(start[0] == 1)

# Define a helper function to return the duration expression for a given itinerary variable
def duration_expr(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4],
           If(city_var == 5, durations[5],
           If(city_var == 6, durations[6],
           If(city_var == 7, durations[7], 0)))))))

# Chain the segments:
# When flying from city A to city B on day X, day X counts for both A and B.
# So, for segment i and i+1: start[i+1] = start[i] + duration(A) - 1.
for i in range(N - 1):
    solver.add(start[i+1] == start[i] + duration_expr(itinerary[i]) - 1)

# The final (last) segment must end at day 22:
solver.add(start[N-1] + duration_expr(itinerary[N-1]) - 1 == 22)

# Allowed flight constraints: For each consecutive pair, the flight from itinerary[i] to itinerary[i+1] must be allowed.
for i in range(N - 1):
    # Build the disjunction of allowed pairs.
    allowed_cond = []
    for (frm, to) in allowed_pairs:
        allowed_cond.append(And(itinerary[i] == frm, itinerary[i+1] == to))
    solver.add(Or(allowed_cond))

# Event constraints:
# Wedding in Frankfurt must be attended between day 16 and day 18.
# That means the Frankfurt segment (city index 7) must cover at least one day in [16,18]:
# If a segment is Frankfurt, then start <= 18 and (start + duration - 1) >= 16.
for i in range(N):
    solver.add(Implies(itinerary[i] == 7, And(start[i] <= 18, start[i] + durations[7] - 1 >= 16)))

# Workshop in Vilnius must be attended between day 18 and day 22.
# So if a segment is Vilnius (city index 6), then its day range [start, start+4] (since duration is 5)
# must intersect [18,22]: start <= 22 and start + 4 >= 18.
for i in range(N):
    solver.add(Implies(itinerary[i] == 6, And(start[i] <= 22, start[i] + durations[6] - 1 >= 18)))

# (Istanbul already is fixed as first and its block will be day 1 to 5, which covers the annual show.)

# Check satisfiability and extract a model if one exists.
if solver.check() == sat:
    model = solver.model()
    # Build a list of segments for the itinerary.
    result = []
    for i in range(N):
        city = model[itinerary[i]].as_long()
        s_day = model[start[i]].as_long()
        dur = durations[city]
        e_day = s_day + dur - 1
        result.append({
            "city": city_names[city],
            "start_day": s_day,
            "end_day": e_day
        })
    itinerary_json = {"itinerary": result}
    print(json.dumps(itinerary_json, indent=2))
else:
    print("No solution found.")