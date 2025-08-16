from z3 import *
import json

# Cities and their required durations.
# City indices: 0: Stuttgart, 1: Bucharest, 2: Geneva, 3: Valencia, 4: Munich
cities = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
durations = [2, 2, 4, 6, 7]  # required days in each city

# Allowed direct flight pairs (bidirectional).
# Each pair (a,b) means you can fly directly between cities a and b.
allowed_pairs = set([
    (2, 4), (4, 2),    # Geneva <-> Munich
    (4, 3), (3, 4),    # Munich <-> Valencia
    (1, 3), (3, 1),    # Bucharest <-> Valencia
    (4, 1), (1, 4),    # Munich <-> Bucharest
    (3, 0), (0, 3),    # Valencia <-> Stuttgart
    (2, 3), (3, 2)     # Geneva <-> Valencia
])

# Helper: Given a Z3 Int city variable, return its duration as a Z3 expression.
def duration_expr(city):
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
              durations[4]))))

# Helper: Return a Z3 boolean that city1->city2 is an allowed direct flight.
def allowed_flight(city1, city2):
    conds = []
    for (a, b) in allowed_pairs:
        conds.append(And(city1 == a, city2 == b))
    return Or(conds)

# Create the Z3 solver.
solver = Solver()

# The itinerary will consist of 5 blocks – one contiguous visit per city.
# We will decide on an ordering of the 5 cities. Each city is visited exactly once.
# On a flight day the itinerary “belongs” to both the origin and destination.
# Let order[i] be the city index for block i.
order = [Int("P%d" % i) for i in range(5)]
for p in order:
    solver.add(And(p >= 0, p < 5))
solver.add(Distinct(order))

# For each block i, let start_days[i] be the first day the block is “active.”
# The first block starts on Day 1.
start_days = [Int("s%d" % i) for i in range(5)]
solver.add(start_days[0] == 1)

# If you are in city A with required days d, and then fly on its last day to B,
# then you spend d days in A (including the flight day) and B starts on that same day.
# So for block i (i>=1): s[i] = s[i-1] + (duration for block i-1) - 1.
for i in range(1, 5):
    solver.add(start_days[i] == start_days[i-1] + duration_expr(order[i-1]) - 1)

# The overall trip lasts 17 days.
# The end day of the last block = start_days[4] + duration_expr(order[4]) - 1  must equal 17.
solver.add(start_days[4] + duration_expr(order[4]) - 1 == 17)

# Add allowed flight transition constraints.
# For every two consecutive blocks, the direct flight between the cities must be allowed.
for i in range(4):
    solver.add(allowed_flight(order[i], order[i+1]))

# Special scheduling constraints:
# (1) "Visit relatives in Geneva between day 1 and day 4" means that if Geneva (index 2)
#     is visited in any block i, then its block must start on or before day 4.
for i in range(5):
    solver.add(Or(order[i] != 2, start_days[i] <= 4))
    
# (2) "Meet your friends at Munich between day 4 and day 10" means that if Munich (index 4)
#     is visited in any block i, then its block must start on or before day 10.
for i in range(5):
    solver.add(Or(order[i] != 4, start_days[i] <= 10))

# Solve the constraints.
if solver.check() == sat:
    m = solver.model()
    # Extract the order and start day for each block.
    order_solution = [m.evaluate(order[i]).as_long() for i in range(5)]
    start_solution = [m.evaluate(start_days[i]).as_long() for i in range(5)]
    
    # Compute the start and end day for each city block.
    # End day for block i is: start_day + duration - 1.
    block_info = []
    for i in range(5):
        city_index = order_solution[i]
        d = durations[city_index]
        s_day = start_solution[i]
        e_day = s_day + d - 1
        block_info.append((cities[city_index], s_day, e_day))
    
    # Build the day-by-day itinerary.
    # For each day from 1 to 17, list the cities (one or two) that are "active" that day.
    itinerary = []
    for day in range(1, 18):
        day_cities = []
        # A day is part of a block if it falls in the interval [start, end] for that block.
        for (city, s_day_val, e_day_val) in block_info:
            if s_day_val <= day <= e_day_val:
                day_cities.append(city)
        itinerary.append({"day": day, "cities": day_cities})
    
    # Output the itinerary as a JSON-formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")