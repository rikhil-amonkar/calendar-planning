from z3 import *
import json

# There are 7 cities:
# 0: Valencia (5 days)
# 1: Riga     (5 days)
# 2: Prague   (3 days) -- must include at least one day between 7 and 9 (i.e. its block [s, s+2] must intersect [7,9])
# 3: Mykonos  (3 days) -- must include at least one day between 1 and 3 (i.e. its block must intersect [1,3])
# 4: Zurich   (5 days)
# 5: Bucharest(5 days)
# 6: Nice     (2 days)

# Allowed direct flights (bidirectional):
#   Mykonos-Nice,
#   Mykonos-Zurich,
#   Prague-Bucharest,
#   Valencia-Bucharest,
#   Zurich-Prague,
#   Riga-Nice,
#   Zurich-Riga,
#   Zurich-Bucharest,
#   Zurich-Valencia,
#   Bucharest-Riga,
#   Prague-Riga,
#   Prague-Valencia,
#   Zurich-Nice

def duration(city):
    # Given a city (an Int sort value 0..6), return its duration.
    return If(city == 0, 5,
           If(city == 1, 5,
           If(city == 2, 3,
           If(city == 3, 3,
           If(city == 4, 5,
           If(city == 5, 5,
           If(city == 6, 2, 0)))))))

def allowed_flight(a, b):
    # Returns a BoolRef that is true if there is a direct flight between cities a and b.
    # The flights are bidirectional.
    return Or(
        # Mykonos (3) and Nice (6)
        And(a == 3, b == 6), And(a == 6, b == 3),
        # Mykonos (3) and Zurich (4)
        And(a == 3, b == 4), And(a == 4, b == 3),
        # Prague (2) and Bucharest (5)
        And(a == 2, b == 5), And(a == 5, b == 2),
        # Valencia (0) and Bucharest (5)
        And(a == 0, b == 5), And(a == 5, b == 0),
        # Zurich (4) and Prague (2)
        And(a == 4, b == 2), And(a == 2, b == 4),
        # Riga (1) and Nice (6)
        And(a == 1, b == 6), And(a == 6, b == 1),
        # Zurich (4) and Riga (1)
        And(a == 4, b == 1), And(a == 1, b == 4),
        # Zurich (4) and Bucharest (5)
        And(a == 4, b == 5), And(a == 5, b == 4),
        # Zurich (4) and Valencia (0)
        And(a == 4, b == 0), And(a == 0, b == 4),
        # Prague (2) and Riga (1)
        And(a == 2, b == 1), And(a == 1, b == 2),
        # Prague (2) and Valencia (0)
        And(a == 2, b == 0), And(a == 0, b == 2),
        # Zurich (4) and Nice (6)
        And(a == 4, b == 6), And(a == 6, b == 4),
        # Bucharest (5) and Riga (1)
        And(a == 5, b == 1), And(a == 1, b == 5)
    )

# We want a 22-day trip.
# Structure: We visit each city exactly once in a certain order.
# For each city visited, we spend its fixed number of days.
# When flying (i.e. switching from one city to the next), the flight happens on the first day
# of the new city’s block which is the same as the last day of the previous city.
#
# Thus if a city (say A) is visited in a block that goes from day s to s+d-1, and then you fly to city B
# on day s+d-1 (so city B’s block starts that day and lasts d' days), then:
# - City A is counted on days s,..., s+d-1  (d days)
# - City B is counted on days s+d-1, ... , s+d-1 + d' - 1  (d' days)
# Overall unique days = d + d' - 1.
#
# The total sum of the durations is 5+5+3+3+5+5+2 = 28.
# With 6 overlaps (one per flight), the unique trip days = 28-6 = 22.

s = Solver()
n = 7  # number of cities

# The itinerary order will be a permutation (list) of the 7 city indices.
perm = [Int(f'perm_{i}') for i in range(n)]
# start_vars[i] will be the start day (of the city block placed at position i in the itinerary)
start_vars = [Int(f'start_{i}') for i in range(n)]

# Constraint: perm is a permutation of 0,...,6.
s.add(Distinct(perm))
for i in range(n):
    s.add(And(perm[i] >= 0, perm[i] < n))

# The first city starts on day 1.
s.add(start_vars[0] == 1)
# For i > 0, the start day of the city at position i equals the previous start day plus (duration of previous city - 1)
for i in range(1, n):
    s.add(start_vars[i] == start_vars[i-1] + duration(perm[i-1]) - 1)

# The last city’s block must end on day 22.
s.add(start_vars[n-1] + duration(perm[n-1]) - 1 == 22)

# Flight transitions: for each consecutive pair in the itinerary, there must be a direct flight.
for i in range(n - 1):
    s.add(allowed_flight(perm[i], perm[i+1]))

# Special event constraints:
# Wedding in Mykonos (city 3) between day 1 and day 3:
# If Mykonos is visited at position i, its block [start_vars[i], start_vars[i]+2] must intersect [1,3].
# Since all trips start at day >= 1, we require start_vars[i] <= 3.
for i in range(n):
    s.add(Implies(perm[i] == 3, start_vars[i] <= 3))

# Visiting relatives in Prague (city 2) between day 7 and day 9:
# Prague is a 3‐day stay, so its block [start, start+2] must have at least one day in {7,8,9}.
# This is equivalent to: start <= 9 and start+2 >= 7.
for i in range(n):
    s.add(Implies(perm[i] == 2, And(start_vars[i] <= 9, start_vars[i] + 2 >= 7)))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    # Mapping from city indices to names and fixed durations.
    city_names = {
         0: "Valencia",
         1: "Riga",
         2: "Prague",
         3: "Mykonos",
         4: "Zurich",
         5: "Bucharest",
         6: "Nice"
    }
    fixed_durations = {0: 5, 1: 5, 2: 3, 3: 3, 4: 5, 5: 5, 6: 2}
    
    # Build the itinerary segments (in the order of the trip).
    segments = []
    for i in range(n):
        city_id = m.evaluate(perm[i]).as_long()
        start_day = m.evaluate(start_vars[i]).as_long()
        d = fixed_durations[city_id]
        segments.append({
            "city": city_names[city_id],
            "start": start_day,
            "end": start_day + d - 1
        })
    
    # Since the flight day is the overlap day between segments,
    # for each trip day from 1 to 22, list all segments (cities) that are “active” on that day.
    itinerary = []
    for day in range(1, 23):
        places_today = []
        for seg in segments:
            if seg["start"] <= day <= seg["end"]:
                places_today.append(seg["city"])
        itinerary.append({"day": day, "places": places_today})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")