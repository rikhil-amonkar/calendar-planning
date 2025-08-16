from z3 import *
import json

# The six cities along with their required stay durations.
# City indices:
# 0: Dublin (5 days)
# 1: Helsinki (3 days)
# 2: Riga (3 days)
# 3: Reykjavik (2 days)
# 4: Vienna (2 days)
# 5: Tallinn (5 days)
cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
durations = [5, 3, 3, 2, 2, 5]

# Allowed direct flights.
# Note: when the description says “A and B” we assume that both A->B and B->A are possible,
# except for the “from Riga to Tallinn” flight which is only allowed in that direction.
allowed_flights = set()
# Helsinki <-> Riga
allowed_flights.add((1, 2))
allowed_flights.add((2, 1))
# Riga -> Tallinn (only one direction)
allowed_flights.add((2, 5))
# Vienna <-> Helsinki
allowed_flights.add((4, 1))
allowed_flights.add((1, 4))
# Riga <-> Dublin
allowed_flights.add((2, 0))
allowed_flights.add((0, 2))
# Vienna <-> Riga
allowed_flights.add((4, 2))
allowed_flights.add((2, 4))
# Reykjavik <-> Vienna
allowed_flights.add((3, 4))
allowed_flights.add((4, 3))
# Helsinki <-> Dublin
allowed_flights.add((1, 0))
allowed_flights.add((0, 1))
# Tallinn <-> Dublin
allowed_flights.add((5, 0))
allowed_flights.add((0, 5))
# Reykjavik <-> Helsinki
allowed_flights.add((3, 1))
allowed_flights.add((1, 3))
# Reykjavik <-> Dublin
allowed_flights.add((3, 0))
allowed_flights.add((0, 3))
# Helsinki <-> Tallinn
allowed_flights.add((1, 5))
allowed_flights.add((5, 1))
# Vienna <-> Dublin
allowed_flights.add((4, 0))
allowed_flights.add((0, 4))

# Create the Z3 solver instance.
solver = Solver()

# We decide the visiting order.
# pos[i] is the city index (0..5) visited at position i (i = 0,...,5).
# The six positions form a permutation of {0,1,2,3,4,5}.
pos = [Int("pos_%d" % i) for i in range(6)]
for p in pos:
    solver.add(And(p >= 0, p < 6))
solver.add(Distinct(*pos))

# We want to schedule the days in a “chain” of segments.
# A flight takes place on the last day of a segment.
# When flying from city A to city B on day X, that day counts for both A and B.
# We define start[i] and end[i] as the start and end days (inclusive) for segment i.
# The duration assigned to a segment is fixed by the intended stay.
start = [Int("start_%d" % i) for i in range(6)]
end = [Int("end_%d" % i) for i in range(6)]

# The trip starts on day 1.
solver.add(start[0] == 1)

# For each segment i, end[i] = start[i] + (duration for that city) - 1.
# Use nested Ifs to select the duration according to the city assigned at pos[i].
for i in range(6):
    solver.add(end[i] == start[i] + (If(pos[i] == 0, durations[0],
                                      If(pos[i] == 1, durations[1],
                                      If(pos[i] == 2, durations[2],
                                      If(pos[i] == 3, durations[3],
                                      If(pos[i] == 4, durations[4],
                                         durations[5]))))) - 1)

# Consecutive segments: the start day of segment i is the same as the flight day,
# which is equal to the end day of segment i-1.
for i in range(1, 6):
    solver.add(start[i] == end[i - 1])

# The final day of the trip is day 15.
solver.add(end[5] == 15)

# Flight connectivity: For every adjacent pair of segments, there must be a direct flight.
for i in range(5):
    flight_options = []
    for (a, b) in allowed_flights:
        flight_options.append(And(pos[i] == a, pos[i + 1] == b))
    solver.add(Or(flight_options))

# Event constraints:
# 1. Annual show in Vienna (city 4) must be attended on either day 2 or day 3.
#    So if a segment is in Vienna then its interval must include day 2 or day 3.
for i in range(6):
    solver.add(Implies(pos[i] == 4,
                       Or(And(start[i] <= 2, end[i] >= 2),
                          And(start[i] <= 3, end[i] >= 3))))

# 2. Meet friends in Helsinki (city 1) between day 3 and day 5.
#    The Helsinki segment must overlap with the interval [3,5].
for i in range(6):
    solver.add(Implies(pos[i] == 1,
                       And(start[i] <= 5, end[i] >= 3)))

# 3. Attend a wedding in Tallinn (city 5) between day 7 and day 11.
for i in range(6):
    solver.add(Implies(pos[i] == 5,
                       And(start[i] <= 11, end[i] >= 7)))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    order = [model.evaluate(pos[i]).as_long() for i in range(6)]
    s_times = [model.evaluate(start[i]).as_long() for i in range(6)]
    e_times = [model.evaluate(end[i]).as_long() for i in range(6)]
    
    # Construct the daily itinerary.
    # For each day from 1 to 15, a day is in a city segment if the day is between its start and end.
    # Note that flight days count for two segments.
    itinerary = []
    for d in range(1, 16):
        cities_today = []
        for i in range(6):
            if s_times[i] <= d <= e_times[i]:
                cities_today.append(cities[order[i]])
        itinerary.append({"day": d, "city": ", ".join(cities_today)})
    
    # Print the itinerary as JSON.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")