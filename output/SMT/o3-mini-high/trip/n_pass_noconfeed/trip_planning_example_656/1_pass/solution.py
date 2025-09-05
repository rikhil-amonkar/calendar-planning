from z3 import *
import json

# Mapping from integer index to city name
city_names = {
    0: "Reykjavik",
    1: "Istanbul",
    2: "Edinburgh",
    3: "Oslo",
    4: "Stuttgart",
    5: "Bucharest"
}

# Duration (in days) needed for each city.
# Note: Because if you fly on the last day of a stay, that day is counted for both cities.
def duration(c):
    return If(c == 0, 5,
           If(c == 1, 4,
           If(c == 2, 5,
           If(c == 3, 2,
           If(c == 4, 3,
           If(c == 5, 5, 0))))))

# Allowed flight connections between cities.
# Each tuple (a, b) means that if you are in city 'a', you can fly directly to city 'b'.
# Note that all flights are bidirectional except the flight from Reykjavik to Stuttgart.
allowed_transitions = [
    (5, 3), (3, 5),      # Bucharest <-> Oslo
    (1, 3), (3, 1),      # Istanbul <-> Oslo
    (0, 4),             # Reykjavik -> Stuttgart (only one-way)
    (5, 1), (1, 5),      # Bucharest <-> Istanbul
    (4, 2), (2, 4),      # Stuttgart <-> Edinburgh
    (1, 2), (2, 1),      # Istanbul <-> Edinburgh
    (3, 0), (0, 3),      # Oslo <-> Reykjavik
    (1, 4), (4, 1),      # Istanbul <-> Stuttgart
    (3, 2), (2, 3)       # Oslo <-> Edinburgh
]

# Create SMT solver
s = Solver()

# We have 6 cities to visit, each city is represented by an integer 0..5.
cities = [Int("city_%d" % i) for i in range(6)]
# Start day for each city visit segment.
starts = [Int("s_%d" % i) for i in range(6)]

# Domain constraints for cities (each city index in 0..5)
for i in range(6):
    s.add(cities[i] >= 0, cities[i] <= 5)

# All cities must be distinct (each visited exactly once)
s.add(Distinct(cities))

# The itinerary timing: 
# If you stay in a city for D days then the flight day is the last day of that stay 
# and is shared with the next city.
# Let s[0] be the start day of the first city; we fix it to Day 1.
s.add(starts[0] == 1)

# For each consecutive city, the start day is:
# start[i+1] = start[i] + duration(city[i]) - 1
for i in range(5):
    s.add(starts[i+1] == starts[i] + duration(cities[i]) - 1)

# The trip lasts exactly 19 days.
# That is: last_day = start[5] + duration(city[5]) - 1 must be 19.
s.add(starts[5] + duration(cities[5]) - 1 == 19)

# Flight (transition) constraints: consecutive cities must be connected by a direct flight.
for i in range(5):
    allowed = []
    for (a, b) in allowed_transitions:
        allowed.append(And(cities[i] == a, cities[i+1] == b))
    s.add(Or(allowed))

# Constraint: Meet friends in Istanbul between day 5 and day 8.
# If a visit is in Istanbul (city index 1) then its visit period [start, start + 4 - 1] must overlap with [5,8].
# Overlap means: start <= 8 and (start + 3) >= 5.
for i in range(6):
    s.add(Implies(cities[i] == 1, And(starts[i] <= 8, starts[i] + 3 >= 5)))

# Constraint: Visit relatives in Oslo between day 8 and day 9.
# For Oslo (city index 3), the visit period [start, start + 2 - 1] must overlap with [8,9].
# In other words: start <= 9 and (start + 1) >= 8.
for i in range(6):
    s.add(Implies(cities[i] == 3, And(starts[i] <= 9, starts[i] + 1 >= 8)))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    # Build the itinerary from the solution.
    itinerary = []
    for i in range(6):
        # Get the city index and its name
        city_val = m[cities[i]].as_long()
        city_name = city_names[city_val]
        # Determine the duration from the SMT model using our if-then definition:
        # (We can also use a simple mapping since durations are fixed)
        if city_val == 0:
            d = 5
        elif city_val == 1:
            d = 4
        elif city_val == 2:
            d = 5
        elif city_val == 3:
            d = 2
        elif city_val == 4:
            d = 3
        elif city_val == 5:
            d = 5

        start_day = m[starts[i]].as_long()
        end_day = start_day + d - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_name})
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))