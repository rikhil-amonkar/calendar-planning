from z3 import *
import json

# Define the cities by indices.
# 0: Mykonos (4 days)
# 1: Nice (3 days, must host conference on days 14 and 16)
# 2: London (2 days)
# 3: Copenhagen (3 days)
# 4: Oslo (5 days, must meet friend on some day between 10 and 14)
# 5: Tallinn (4 days)
cities = [0, 1, 2, 3, 4, 5]
durations = {0: 4, 1: 3, 2: 2, 3: 3, 4: 5, 5: 4}
city_names = {0: "Mykonos", 1: "Nice", 2: "London",
              3: "Copenhagen", 4: "Oslo", 5: "Tallinn"}

# Allowed direct flights (bidirectional) as given:
# London-Copenhagen, Copenhagen-Tallinn, Tallinn-Oslo, Mykonos-London,
# Oslo-Nice, London-Nice, Mykonos-Nice, London-Oslo, Copenhagen-Nice, Copenhagen-Oslo.
allowed_flights = [
    (0, 2), (2, 0),   # Mykonos <-> London
    (0, 1), (1, 0),   # Mykonos <-> Nice
    (2, 3), (3, 2),   # London <-> Copenhagen
    (3, 5), (5, 3),   # Copenhagen <-> Tallinn
    (5, 4), (4, 5),   # Tallinn <-> Oslo
    (4, 1), (1, 4),   # Oslo <-> Nice
    (2, 1), (1, 2),   # London <-> Nice
    (2, 4), (4, 2),   # London <-> Oslo
    (3, 1), (1, 3),   # Copenhagen <-> Nice
    (3, 4), (4, 3)    # Copenhagen <-> Oslo
]

# We plan to visit all 6 cities in 6 segments.
# Each segment i is associated with a city (order[i]) and has a start day s[i].
# When flying from segment i to segment i+1 on day X, that day (X) is counted in both segments.
# Thus, if a segment has required duration d, its days are s[i] ... (s[i] + d - 1).
# And we enforce that s[0] = 1 and, because there are 5 flights (overlap days) in 6 segments,
# the overall schedule ends on day 16.
order = [Int(f"order_{i}") for i in range(6)]
s_vars = [Int(f"s_{i}") for i in range(6)]

solver = Solver()

# Domain constraints for the city order and start days.
for i in range(6):
    solver.add(And(order[i] >= 0, order[i] < 6))
    # A start day must be between 1 and 16.
    solver.add(s_vars[i] >= 1, s_vars[i] <= 16)

# The 6 cities must all be visited exactly once.
solver.add(Distinct(order))

# The first segment starts on day 1.
solver.add(s_vars[0] == 1)

# Force Nice (city 1) to be visited in the last segment.
solver.add(order[5] == 1)
# In order for Nice (which lasts 3 days) to cover the conference days (14 and 16),
# its start day must be 14 (14, 15, 16).
solver.add(s_vars[5] == 14)

# Define a helper to compute the end day of segment i.
# end_i = s_i + duration(city) - 1.
def end_expr(i):
    return Sum([If(order[i] == c, s_vars[i] + durations[c] - 1, 0) for c in cities])

# Consecutive segments: flying from one to the next means the next segment’s start day
# must equal the previous segment’s end day.
for i in range(5):
    solver.add(s_vars[i+1] == end_expr(i))

# The overall schedule must end on day 16.
solver.add(end_expr(5) == 16)

# For each flight between adjacent segments, ensure that there is a direct connection.
for i in range(5):
    possible_flights = []
    for (a, b) in allowed_flights:
        possible_flights.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(possible_flights))

# Oslo friend meeting constraint:
# If a segment is Oslo (city 4), then some day between 10 and 14 is spent in Oslo.
# That is, the Oslo interval [s, s + 5 - 1] must intersect the interval [10, 14].
for i in range(6):
    solver.add(Implies(order[i] == 4, And(s_vars[i] <= 14, s_vars[i] + durations[4] - 1 >= 10)))

# (The Nice conference constraint is automatically satisfied by forcing Nice as the last segment
# with start day 14 and end day 16.)

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    segments = []
    for i in range(6):
        city_idx = model[order[i]].as_long()
        start_day = model[s_vars[i]].as_long()
        end_day = start_day + durations[city_idx] - 1
        segments.append((city_idx, start_day, end_day))
    
    # Build a day-to-city mapping.
    # If a day is used as a flight day (i.e. it falls in two segments), list both cities.
    itinerary = {}
    for seg in segments:
        city_idx, s_day, e_day = seg
        for d in range(s_day, e_day + 1):
            if d in itinerary:
                if city_names[city_idx] not in itinerary[d]:
                    itinerary[d].append(city_names[city_idx])
            else:
                itinerary[d] = [city_names[city_idx]]
    
    # Create a sorted list of day mappings.
    itinerary_list = []
    for day in sorted(itinerary.keys()):
        # To match the example style, if there is only one city that day, we output "place",
        # otherwise we output "places" as a list.
        if len(itinerary[day]) == 1:
            itinerary_list.append({"day": day, "place": itinerary[day][0]})
        else:
            itinerary_list.append({"day": day, "places": itinerary[day]})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")