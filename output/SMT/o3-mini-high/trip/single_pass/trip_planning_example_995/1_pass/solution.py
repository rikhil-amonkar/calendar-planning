from z3 import *
import json

# City names (we assign indices for convenience)
cities = ["Barcelona", "Oslo", "Stuttgart", "Venice", "Split", "Brussels", "Copenhagen"]

# Required durations (if no flight were taken they would add up to 22 days;
# note that every flight day is counted twice so that 7 segments gives 22-6=16 total days)
durations = {
    "Barcelona": 3,
    "Oslo": 2,
    "Stuttgart": 3,
    "Venice": 4,
    "Split": 4,
    "Brussels": 3,
    "Copenhagen": 3
}

# Allowed direct flight connections (each unordered pair is allowed)
# We use indices corresponding to the cities list.
# (For example, "Barcelona" is index 0, "Oslo" is 1, etc.)
allowed_pairs = [
    (0,1), (1,0),                   # Barcelona - Oslo
    (0,6), (6,0),                   # Barcelona - Copenhagen
    (0,3), (3,0),                   # Barcelona - Venice
    (0,4), (4,0),                   # Barcelona - Split
    (0,2), (2,0),                   # Barcelona - Stuttgart
    (0,5), (5,0),                   # Barcelona - Brussels
    (1,4), (4,1),                   # Oslo - Split
    (1,3), (3,1),                   # Oslo - Venice
    (1,6), (6,1),                   # Oslo - Copenhagen
    (1,5), (5,1),                   # Oslo - Brussels
    (4,6), (6,4),                   # Split - Copenhagen
    (6,5), (5,6),                   # Copenhagen - Brussels
    (6,2), (2,6),                   # Copenhagen - Stuttgart
    (6,3), (3,6),                   # Copenhagen - Venice
    (5,3), (3,5),                   # Brussels - Venice
    (4,2), (2,4),                   # Split - Stuttgart
    (3,2), (2,3)                    # Venice - Stuttgart
]

# There will be 7 segments in our itinerary.
n_segments = 7

# Create Z3 variables for the route ordering.
# route[i] is an integer (0..6) representing which city is visited in segment i.
route = [Int("route_%d" % i) for i in range(n_segments)]
# Also create variables for the start day of each segment.
# A segment is visited from start[i] to start[i] + (duration of that city) - 1.
start_time = [Int("start_%d" % i) for i in range(n_segments)]

s = Solver()

# Each route value is between 0 and 6.
for r in route:
    s.add(r >= 0, r < len(cities))
# They must form a permutation
s.add(Distinct(route))

# Fix the two cities with extra constraints:
#  – Barcelona must be first (to attend the annual show from day 1-3)
#  – Oslo must be visited in a way that allows meeting friends between day 3 and 4.
s.add(route[0] == cities.index("Barcelona"))
s.add(route[1] == cities.index("Oslo"))
# (Since segment_1 will have start_time[1] computed from segment_0, Oslo will be from day 3–4.)

# Define a function to “lookup” the duration for a given city index.
def duration_for(r):
    return If(r == 0, durations["Barcelona"],
           If(r == 1, durations["Oslo"],
           If(r == 2, durations["Stuttgart"],
           If(r == 3, durations["Venice"],
           If(r == 4, durations["Split"],
           If(r == 5, durations["Brussels"],
           durations["Copenhagen"]))))))

# The start time for the first segment is day 1.
s.add(start_time[0] == 1)
# For each segment i>0, the flight from the previous city happens on the day start_time[i],
# which is the last day of the previous city. (Flight day counts in both cities.)
for i in range(1, n_segments):
    d_prev = duration_for(route[i-1])
    # The i-th segment starts on the same day the (i-1)th segment ends.
    s.add(start_time[i] == start_time[i-1] + d_prev - 1)

# The itinerary must last exactly 16 days.
# The last segment i=n_segments-1 has end day = start_time + duration - 1.
s.add(start_time[n_segments-1] + duration_for(route[n_segments-1]) - 1 == 16)

# Direct flight constraint for each consecutive pair.
for i in range(n_segments - 1):
    # The pair (route[i], route[i+1]) must be one of the allowed pairs.
    conds = []
    for (a, b) in allowed_pairs:
        conds.append(And(route[i] == a, route[i+1] == b))
    s.add(Or(conds))

# Brussels meeting constraint:
# If Brussels (index 5) is visited in segment i then the start day must be between 7 and 11,
# so that the 3‑day stay (days start to start+2) includes some day between 9 and 11.
for i in range(n_segments):
    s.add(Implies(route[i] == cities.index("Brussels"),
                  And(start_time[i] >= 7, start_time[i] <= 11)))

# (The meeting in Oslo between day 3–4 is already satisfied by the choice of
# Barcelona first (3–day stay) and Oslo second (2‑day stay on days 3–4).)

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    # Get the route order (as city names) and the start times.
    sol_route = [m.evaluate(route[i]).as_long() for i in range(n_segments)]
    sol_starts = [m.evaluate(start_time[i]).as_long() for i in range(n_segments)]
    # Compute the duration for each segment (using the durations dictionary).
    sol_durations = [durations[cities[sol_route[i]]] for i in range(n_segments)]
    
    # Build a day-by-day itinerary.
    # On each day from 1 to 16, list the cities “active” that day.
    # A segment covers days start to start+duration-1.
    itinerary = []
    # There are 16 days in the trip.
    for d in range(1, 17):
        day_cities = []
        for i in range(n_segments):
            seg_start = sol_starts[i]
            seg_end = sol_starts[i] + sol_durations[i] - 1
            if d >= seg_start and d <= seg_end:
                day_cities.append(cities[sol_route[i]])
        itinerary.append({"day": d, "cities": day_cities})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")