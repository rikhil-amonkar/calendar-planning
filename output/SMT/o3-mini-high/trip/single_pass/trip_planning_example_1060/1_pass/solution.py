from z3 import *

# Define the eight cities (indexed 0..7) and their fixed durations.
# 0: Reykjavik (4 days)
# 1: Stuttgart (4 days)
# 2: Istanbul (4 days)
# 3: Vilnius (4 days)
# 4: Seville (3 days)
# 5: Geneva (5 days)
# 6: Valencia (5 days)
# 7: Munich (3 days)
cities = ["Reykjavik", "Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich"]
durations = [4, 4, 4, 4, 3, 5, 5, 3]

# Allowed flight connections.
# Note: For a flight taken on day X, that day counts for both the departure and arrival city.
# We express allowed transitions as (a,b) where a->b is allowed.
# For bidirectional flights, include both ordered pairs.
allowed_pairs = [
    # "from Reykjavik to Stuttgart" (directional only)
    (0, 1),
    # Reykjavik <-> Munich
    (0, 7), (7, 0),
    # Stuttgart <-> Valencia
    (1, 6), (6, 1),
    # Stuttgart <-> Istanbul
    (1, 2), (2, 1),
    # Geneva <-> Istanbul
    (5, 2), (2, 5),
    # Munich <-> Geneva
    (7, 5), (5, 7),
    # Istanbul <-> Vilnius
    (2, 3), (3, 2),
    # Valencia <-> Seville
    (6, 4), (4, 6),
    # Valencia <-> Istanbul
    (6, 2), (2, 6),
    # "from Vilnius to Munich" (directional only)
    (3, 7),
    # Seville <-> Munich
    (4, 7), (7, 4),
    # Munich <-> Istanbul
    (7, 2), (2, 7),
    # Valencia <-> Geneva
    (6, 5), (5, 6),
    # Valencia <-> Munich
    (6, 7), (7, 6)
]

def allowed_flight(a, b):
    # a, b are Z3 Ints representing city indices.
    # Return a BoolRef that is True if (a,b) is one of the allowed transitions.
    conds = []
    for (u, v) in allowed_pairs:
        conds.append(And(a == u, b == v))
    return Or(*conds)

# We'll have 8 positions in the itinerary.
# order[i] is the city index visited in the i-th block.
order = [Int(f"order_{i}") for i in range(8)]
s = Solver()

# Each order element must be between 0 and 7.
for o in order:
    s.add(o >= 0, o < 8)
# All cities are visited exactly once.
s.add(Distinct(order))

# Imposed fixed positions from the special date requirements:
# - The trip must begin in Reykjavik so that the workshop (day 1-4) is attended.
s.add(order[0] == 0)  # Reykjavik
# - Stuttgart (with its day4 and day7 conference) must be visited immediately after.
s.add(order[1] == 1)  # Stuttgart
# - The annual show in Munich (day 13-15) forces Munich to appear in a position that yields start day 13.
#   (The only possibility turns out to be the 5th block, i.e. order[4].)
s.add(order[4] == 7)  # Munich
# - Visiting relatives in Istanbul between day 19 and 22 forces Istanbul to start exactly on day 19.
#   (This forces Istanbul into the 7th block, i.e. order[6].)
s.add(order[6] == 2)  # Istanbul

# Define a helper function to return the constant duration for a given city variable.
def city_duration(city):
    # city is an Int; use If-then-else chain.
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
           If(city == 4, durations[4],
           If(city == 5, durations[5],
           If(city == 6, durations[6],
           If(city == 7, durations[7],
              0)))))))

# We now compute the start day for each block.
# When flying from city A to city B on the same day, that day counts for both.
# So if block i starts on day d, it lasts for duration d_i days (d ... d + dur - 1)
# and the next block starts on: start[i+1] = d + (dur - 1) (i.e. same as the flight day).
start_days = [Int(f"start_{i}") for i in range(8)]
# The trip always starts on day 1.
s.add(start_days[0] == 1)
# For each subsequent block, the start day is:
for i in range(1, 8):
    # start[i] = start[i-1] + (duration(order[i-1]) - 1)
    s.add(start_days[i] == start_days[i-1] + (city_duration(order[i-1]) - 1))

# Total trip: final block from start[7] lasts city_duration(order[7]) days.
# The overall end day is: start_7 + (duration - 1) and must equal 25.
final_day = start_days[7] + (city_duration(order[7]) - 1)
s.add(final_day == 25)

# Now add the special start-day constraints:
# Stuttgart (city 1) must have its block covering day 4 and day 7.
# Since Stuttgart is fixed as order[1], its start day must be 4.
s.add(start_days[1] == 4)
# Munich (city 7) must start on day 13.
# Munich is fixed as order[4]; so start_days[4] must equal 13.
s.add(start_days[4] == 13)
# Istanbul (city 2) must start on day 19.
# Istanbul is fixed as order[6]; so start_days[6] must equal 19.
s.add(start_days[6] == 19)
# Reykjavik (city 0) must be visited early enough so that a workshop between day1-4 is possible.
# (Since it is the first block starting on day 1, this is automatically satisfied.)

# Flight connection constraints: For every consecutive pair, there must be a direct flight.
for i in range(7):
    s.add(allowed_flight(order[i], order[i+1]))

# (Optional) For debugging, one could also add printing constraints about the computed start_days,
# but the key constraints above already force the unique solution.

if s.check() == sat:
    m = s.model()
    # Extract the itinerary: each block's city, and compute its [start, end] interval.
    itinerary = []
    # Compute start and end days from the model.
    # Note: for each block i, end = start_days[i] + duration - 1.
    # When blocks share a flight day, that day appears as the end of block i and the start of block i+1.
    blocks = []
    for i in range(8):
        city_index = m.evaluate(order[i]).as_long()
        city_name = cities[city_index]
        start_day = m.evaluate(start_days[i]).as_long()
        dur = None
        # Get the constant duration for this city from our durations list.
        dur = durations[city_index]
        end_day = start_day + dur - 1
        blocks.append((city_name, start_day, end_day))
    # Prepare the itinerary list as a list of dictionaries.
    for (city_name, dstart, dend) in blocks:
        itinerary.append({"day": f"{dstart}-{dend}", "place": city_name})
    
    import json
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")