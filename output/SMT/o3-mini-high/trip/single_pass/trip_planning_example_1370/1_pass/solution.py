from z3 import *
import json

# Define the cities and their properties.
cities = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]
# Map each city to its required number of days.
durations = {
    "Santorini": 5,
    "Krakow": 5,
    "Paris": 5,
    "Vilnius": 3,
    "Munich": 5,
    "Geneva": 2,
    "Amsterdam": 4,
    "Budapest": 5,
    "Split": 4
}
# For convenience, assign each city an index corresponding to its position in the 'cities' list.
# 0: Santorini, 1: Krakow, 2: Paris, 3: Vilnius, 4: Munich,
# 5: Geneva, 6: Amsterdam, 7: Budapest, 8: Split

# Helper: Given an Int expression representing a city (an integer 0..8), return its duration.
def get_duration(city_int):
    return If(city_int == 0, 5,
           If(city_int == 1, 5,
           If(city_int == 2, 5,
           If(city_int == 3, 3,
           If(city_int == 4, 5,
           If(city_int == 5, 2,
           If(city_int == 6, 4,
           If(city_int == 7, 5, 4))))))))

# The allowed flights.
# For each flight leg (A->B) we require that there is a direct flight.
# Note: For entries like "Paris and Krakow", we allow both directions.
allowed_flights = [
    (2, 1), (1, 2),         # Paris <-> Krakow
    (2, 6), (6, 2),         # Paris <-> Amsterdam
    (2, 8), (8, 2),         # Paris <-> Split
    (3, 4),                # from Vilnius -> Munich (only one way)
    (2, 5), (5, 2),         # Paris <-> Geneva
    (6, 5), (5, 6),         # Amsterdam <-> Geneva
    (4, 8), (8, 4),         # Munich <-> Split
    (8, 1), (1, 8),         # Split <-> Krakow
    (4, 6), (6, 4),         # Munich <-> Amsterdam
    (7, 6), (6, 7),         # Budapest <-> Amsterdam
    (8, 5), (5, 8),         # Split <-> Geneva
    (3, 8), (8, 3),         # Vilnius <-> Split
    (4, 5), (5, 4),         # Munich <-> Geneva
    (4, 1), (1, 4),         # Munich <-> Krakow
    (1, 3),                # from Krakow -> Vilnius (only one way)
    (3, 6), (6, 3),         # Vilnius <-> Amsterdam
    (7, 2), (2, 7),         # Budapest <-> Paris
    (1, 6), (6, 1),         # Krakow <-> Amsterdam
    (3, 2), (2, 3),         # Vilnius <-> Paris
    (7, 5), (5, 7),         # Budapest <-> Geneva
    (8, 6), (6, 8),         # Split <-> Amsterdam
    (0, 5), (5, 0),         # Santorini <-> Geneva
    (6, 0), (0, 6),         # Amsterdam <-> Santorini
    (4, 7), (7, 4),         # Munich <-> Budapest
    (4, 2), (2, 4)          # Munich <-> Paris
]

# Create the Z3 solver.
solver = Solver()

num_blocks = len(cities)  # 9 blocks to visit 9 cities.

# Create the decision variables:
# seq[i] will be the city (0..8) visited in the i-th block.
seq = [Int(f"seq_{i}") for i in range(num_blocks)]
# start[i] will be the start day of the i-th block.
start = [Int(f"start_{i}") for i in range(num_blocks)]

# Constrain the city sequence: each city index must be between 0 and 8 and all must be distinct.
for i in range(num_blocks):
    solver.add(seq[i] >= 0, seq[i] <= 8)
solver.add(Distinct(seq))

# The itinerary runs from day 1 to day 30.
# Set the first block's start day.
solver.add(start[0] == 1)
# For each consecutive block, the start day is the previous block’s start day plus its duration minus 1,
# because the flight day counts for both cities.
for i in range(num_blocks - 1):
    solver.add(start[i+1] == start[i] + get_duration(seq[i]) - 1)
# The last block must end on day 30.
# End day of block i is start[i] + duration(seq[i]) - 1.
solver.add(start[num_blocks - 1] + get_duration(seq[num_blocks - 1]) - 1 == 30)

# Add the festival / meet-up constraints.
# Santorini: Must stay 5 days and at least one of those days (its block) overlaps with days 25 to 29.
for i in range(num_blocks):
    # If this block is Santorini (index 0), then its interval: [start, start+4] must intersect [25,29].
    solver.add(Implies(seq[i] == 0, And(start[i] <= 29, start[i] + 4 >= 25)))

# Krakow: Must stay 5 days and attend a wedding between day 18 and day 22.
for i in range(num_blocks):
    solver.add(Implies(seq[i] == 1, And(start[i] <= 22, start[i] + 4 >= 18)))

# Paris: Must stay 5 days and meet a friend between day 11 and day 15.
for i in range(num_blocks):
    solver.add(Implies(seq[i] == 2, And(start[i] <= 15, start[i] + 4 >= 11)))

# Add the flight (direct connection) constraints between consecutive cities.
for i in range(num_blocks - 1):
    # For the transition from block i to block i+1, the pair (seq[i], seq[i+1]) must be an allowed flight.
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(seq[i] == frm, seq[i+1] == to))
    solver.add(Or(flight_options))

# At this point, the model fully encodes:
# - The order (permutation) of cities.
# - The duration and overlapping day computations.
# - Flight legs that are allowed.
# - Special time window requirements for Santorini, Krakow, and Paris.

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Build the itinerary: For each block, compute the city name, start day, and end day.
    for i in range(num_blocks):
        city_index = model.eval(seq[i]).as_long()
        city_name = cities[city_index]
        s_day = model.eval(start[i]).as_long()
        # Get the duration from our durations dictionary using the city name.
        d = durations[city_name]
        end_day = s_day + d - 1
        itinerary.append({
            "city": city_name,
            "start_day": s_day,
            "end_day": end_day
        })
    # Prepare the JSON output.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")