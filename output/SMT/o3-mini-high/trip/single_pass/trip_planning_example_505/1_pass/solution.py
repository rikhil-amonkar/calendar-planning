from z3 import Solver, Int, If, And, Or, Distinct, sat
import json

# Cities (with indices)
# 0: Prague (4 days)
# 1: Stuttgart (2 days)
# 2: Split   (2 days)
# 3: Krakow  (2 days)
# 4: Florence (2 days)
city_names = {0: "Prague", 1: "Stuttgart", 2: "Split", 3: "Krakow", 4: "Florence"}
durations = {0: 4, 1: 2, 2: 2, 3: 2, 4: 2}

# Allowed flight pairs (bidirectional)
# Note: a flight between A and B is allowed if the unordered pair {A, B} is in allowed_pairs.
allowed_pairs = [
    (1, 2),  # Stuttgart <-> Split
    (0, 4),  # Prague <-> Florence
    (1, 3),  # Stuttgart <-> Krakow
    (2, 3),  # Split <-> Krakow
    (0, 2),  # Prague <-> Split
    (0, 3)   # Prague <-> Krakow
]
# For convenience, we will consider both orders.
def allowed_transition(a, b):
    conds = []
    for (x, y) in allowed_pairs:
        conds.append(And(a == x, b == y))
        conds.append(And(a == y, b == x))
    return Or(*conds)

# Create a solver instance
s = Solver()

# We have 5 positions in the itinerary corresponding to the 5 cities (each visited once).
order = [Int("order_%i" % i) for i in range(5)]
# For each position, we record the start day (flight arrival day, which is also the flight departure day from the previous city)
start_days = [Int("start_%i" % i) for i in range(5)]

# Add constraints that order is a permutation of [0,1,2,3,4]
for i in range(5):
    s.add(order[i] >= 0, order[i] <= 4)
s.add(Distinct(order))

# The itinerary is built by contiguous segments with an overlap on each flight day.
# The first city's period starts on day 1.
s.add(start_days[0] == 1)
# For positions 1..4, the start day is the previous city's end day.
# End day of a city = start_day + (its duration) - 1.
for i in range(1, 5):
    # duration of the previous city depends on which city it is:
    s.add(start_days[i] == start_days[i-1] + If(order[i-1] == 0, durations[0], durations[1]) - 1)
    # Note: for i-1, if it is not Prague (index 0), the duration is 2.
    
# The final day of the last city must be day 8.
# End day of city in position 4 = start_days[4] + (its duration) - 1.
s.add(start_days[4] + If(order[4] == 0, durations[0], durations[1]) - 1 == 8)

# Flight constraints: For each pair of consecutive cities, there must be a direct (allowed) flight.
for i in range(4):
    s.add(allowed_transition(order[i], order[i+1]))

# Wedding in Stuttgart must be attended between day 2 and day 3.
# If Stuttgart (index 1) is visited at a given position, its 2-day interval is [start, start+1]
# and we require that either day 2 or day 3 is in that interval.
for i in range(5):
    s.add(If(order[i] == 1,
             Or(start_days[i] == 1, start_days[i] == 2, start_days[i] == 3),
             True))
    # Explanation:
    #  - If Stuttgart is scheduled at start day 1, its days are [1,2] (day2 is included).
    #  - If start is 2, days [2,3] (both 2 and 3 are included).
    #  - If start is 3, days [3,4] (day3 is included).
    # Any start >= 4 would miss the wedding window.

# Meeting friends in Split: must be between day 3 and day 4.
# Split (index 2) has a 2-day interval and must include day 3 or day 4.
for i in range(5):
    s.add(If(order[i] == 2,
             Or(start_days[i] == 2, start_days[i] == 3, start_days[i] == 4),
             True))

# (Optional) Ensure that start_days are positive and at most 8.
for st in start_days:
    s.add(st >= 1, st <= 8)

# Try to solve the constraints.
if s.check() == sat:
    m = s.model()
    # Recover the order and start day values.
    order_val = [m.evaluate(order[i]).as_long() for i in range(5)]
    start_val = [m.evaluate(start_days[i]).as_long() for i in range(5)]
    
    # Compute each city's interval (start and end day) based on the chosen order.
    itinerary_segments = []
    for i in range(5):
        city = order_val[i]
        dur = durations[city]  # if city is Prague (0), duration is 4; else 2.
        seg_start = start_val[i]
        seg_end = seg_start + dur - 1
        itinerary_segments.append({
            "city": city_names[city],
            "start": seg_start,
            "end": seg_end
        })
    
    # Build a day-by-day itinerary for days 1..8.
    # On a flight day (transition day) the traveler is in both the departing and arriving city.
    # So for each day, include any city for which day is between its start and end (inclusive).
    day_itinerary = []
    for day in range(1, 9):
        cities_today = []
        for segment in itinerary_segments:
            if segment["start"] <= day <= segment["end"]:
                cities_today.append(segment["city"])
        # Sort the cities to have a consistent order
        cities_today = sorted(cities_today)
        day_itinerary.append({"day": day, "cities": cities_today})
    
    result = {"itinerary": day_itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")