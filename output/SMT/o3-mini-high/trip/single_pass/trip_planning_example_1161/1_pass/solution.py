from z3 import *
import json

# There are 8 cities with fixed durations:
# 0: Oslo (2 days)
# 1: Dubrovnik (3 days) – must cover days 2–4 (i.e. start=2 so that 2,3,4)
# 2: Helsinki (2 days)
# 3: Vilnius (2 days)
# 4: Krakow (5 days)
# 5: Paris (2 days)
# 6: Madrid (5 days)
# 7: Mykonos (4 days) – must be visited between day15 and day18 (i.e. start=15 so that days 15-18)
cities = ["Oslo", "Dubrovnik", "Helsinki", "Vilnius", "Krakow", "Paris", "Madrid", "Mykonos"]
durations = [2, 3, 2, 2, 5, 2, 5, 4]

# Allowed direct flights (we assume symmetry) as unordered pairs.
allowed_edges = [
    (0,4),   # Oslo - Krakow
    (0,5),   # Oslo - Paris
    (5,6),   # Paris - Madrid
    (2,3),   # Helsinki - Vilnius
    (0,6),   # Oslo - Madrid
    (0,2),   # Oslo - Helsinki
    (2,4),   # Helsinki - Krakow
    (1,2),   # Dubrovnik - Helsinki
    (1,6),   # Dubrovnik - Madrid
    (0,1),   # Oslo - Dubrovnik
    (4,5),   # Krakow - Paris
    (6,7),   # Madrid - Mykonos
    (0,3),   # Oslo - Vilnius
    (3,4),   # Vilnius - Krakow  (via "from Krakow to Vilnius")
    (2,5),   # Helsinki - Paris
    (3,5),   # Vilnius - Paris
    (2,6)    # Helsinki - Madrid
]

# Required start days for specific cities.
# Dubrovnik must be in [day2, day3, day4] so its block of 3 days must start at day2.
# Mykonos must be visited between day15 and day18 so its block must be exactly day15-18.
req_start = {1: 2, 7: 15}

# Create a solver instance.
solver = Solver()

# We will determine a permutation (ordering) of the 8 cities.
# order[i] is the city (index) at the i-th block of the trip.
order = [Int(f"order_{i}") for i in range(8)]
for o in order:
    solver.add(And(o >= 0, o < 8))
solver.add(Distinct(order))

# Additional forced orders:
# Meet friends in Oslo between day1 and day2 – force Oslo as the first city.
solver.add(order[0] == 0)
# And to ensure the Mykonos relatives constraint, force Mykonos to be the last city.
solver.add(order[7] == 7)

# For each city block we also decide its start day.
# The idea is that if city block i has start day S, then it runs for "duration" days
# and when you fly on the last day (which counts for both cities),
# the next block starts.
start = [Int(f"start_{i}") for i in range(8)]
for s in start:
    solver.add(And(s >= 1, s <= 18))

# The trip begins on day 1.
solver.add(start[0] == 1)

# For each block i from 0 to 6, the next block’s start is the same as the current block’s end.
# (Remember: if a city block runs from S to S+L-1, then flying on day S+L-1 means
#  that day counts for both cities.)
for i in range(7):
    # Since the duration depends on the city in position order[i],
    # we write: start[i+1] = start[i] + durations[ order[i] ] - 1.
    solver.add(start[i+1] == Sum([If(order[i] == city, start[i] + durations[city] - 1, 0)
                                  for city in range(8)]))

# The last block must end on day 18.
# Because order[7] is forced to be Mykonos (index 7) which lasts 4 days:
solver.add(start[7] + durations[7] - 1 == 18)

# For cities with prescribed start days (to meet special day constraints),
# add: if block i is that city then its start must equal the required day.
for i in range(8):
    for city, req in req_start.items():
        solver.add(Implies(order[i] == city, start[i] == req))

# Add flight constraints along the route.
# For each adjacent pair (order[i], order[i+1]), ensure there is a direct flight.
for i in range(7):
    flight_options = []
    for (a, b) in allowed_edges:
        # We allow either direction.
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    solver.add(Or(flight_options))

# Solve the scheduling constraints.
if solver.check() == sat:
    model = solver.model()
    # Extract the ordering and start days.
    order_sol = [model.evaluate(order[i]).as_long() for i in range(8)]
    start_sol = [model.evaluate(start[i]).as_long() for i in range(8)]
    
    # For each city block, compute its interval.
    # The block for a city lasts from start day s to s + duration - 1.
    blocks = []
    for i, city_index in enumerate(order_sol):
        city_name = cities[city_index]
        s_day = start_sol[i]
        e_day = s_day + durations[city_index] - 1
        blocks.append((city_name, s_day, e_day))
    
    # Build an itinerary: for each day (1 to 18) list the cities in which you are present.
    # (On flight days the day appears in both the departing and arriving city.)
    itinerary_by_day = {day: [] for day in range(1, 19)}
    for city_name, s_day, e_day in blocks:
        for day in range(s_day, e_day + 1):
            itinerary_by_day[day].append(city_name)
    
    # Create a list of day-to-city mappings.
    itinerary = []
    for day in range(1, 19):
        itinerary.append({"day": day, "cities": itinerary_by_day[day]})
    
    # Output the itinerary as a JSON-formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")