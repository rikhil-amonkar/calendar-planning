from z3 import *
import json

# Define the cities and their required durations.
cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
durations = {
    "Copenhagen": 5,
    "Geneva": 3,
    "Mykonos": 2,
    "Naples": 4,
    "Prague": 2,
    "Dubrovnik": 3,
    "Athens": 4,
    "Santorini": 5,
    "Brussels": 4,
    "Munich": 5
}

# Specify allowed direct flights. (Treat them as undirected.)
allowed_flights = [
    ("Copenhagen", "Dubrovnik"),
    ("Brussels", "Copenhagen"),
    ("Prague", "Geneva"),
    ("Athens", "Geneva"),
    ("Naples", "Dubrovnik"),
    ("Athens", "Dubrovnik"),
    ("Geneva", "Mykonos"),
    ("Naples", "Mykonos"),
    ("Naples", "Copenhagen"),
    ("Munich", "Mykonos"),
    ("Naples", "Athens"),
    ("Prague", "Athens"),
    ("Santorini", "Geneva"),
    ("Athens", "Santorini"),
    ("Naples", "Munich"),
    ("Prague", "Copenhagen"),
    ("Brussels", "Naples"),
    ("Athens", "Mykonos"),
    ("Athens", "Copenhagen"),
    ("Naples", "Geneva"),
    ("Dubrovnik", "Munich"),
    ("Brussels", "Munich"),
    ("Prague", "Brussels"),
    ("Brussels", "Athens"),
    ("Athens", "Munich"),
    ("Geneva", "Munich"),
    ("Copenhagen", "Munich"),
    ("Brussels", "Geneva"),
    ("Copenhagen", "Geneva"),
    ("Prague", "Munich"),
    ("Copenhagen", "Santorini"),
    ("Naples", "Santorini"),
    ("Geneva", "Dubrovnik")
]

s = Solver()

# We will decide an order (a permutation) of the 10 cities.
# seg[i] (for i=0,...,9) will be an integer in 0..9 indexing the city in "cities".
seg = [Int("seg_%d" % i) for i in range(10)]
for i in range(10):
    s.add(And(seg[i] >= 0, seg[i] < 10))
s.add(Distinct(seg))

# We also introduce the start day for each segment.
# The idea is that when you begin staying in a city you are there from that start day
# until (start + duration - 1).  When you fly on the day of transition the day counts for both.
S_vars = [Int("S_%d" % i) for i in range(10)]
s.add(S_vars[0] == 1)  # The trip begins on day 1.

# Helper: express the duration of the city in a segment as a Z3 expression.
def duration_expr(city):
    return If(city == 0, durations["Copenhagen"],
           If(city == 1, durations["Geneva"],
           If(city == 2, durations["Mykonos"],
           If(city == 3, durations["Naples"],
           If(city == 4, durations["Prague"],
           If(city == 5, durations["Dubrovnik"],
           If(city == 6, durations["Athens"],
           If(city == 7, durations["Santorini"],
           If(city == 8, durations["Brussels"],
           If(city == 9, durations["Munich"], 0)))))))))


# Link the segments’ start days.  If segment i starts on S_i and lasts d days,
# then the next segment starts on the same day as the last day of segment i (flight day overlap).
for i in range(1, 10):
    s.add(S_vars[i] == S_vars[i-1] + duration_expr(seg[i-1]) - 1)
# Total itinerary has 28 days.  (Because overall days = S_last + duration_last - 1.)
s.add(S_vars[9] + duration_expr(seg[9]) - 1 == 28)

# Flight connectivity: consecutive cities must be connected by a direct (allowed) flight.
for i in range(9):
    conds = []
    for (a, b) in allowed_flights:
        a_index = cities.index(a)
        b_index = cities.index(b)
        # Add both orders since flights are undirected.
        conds.append(And(seg[i] == a_index, seg[i+1] == b_index))
        conds.append(And(seg[i] == b_index, seg[i+1] == a_index))
    s.add(Or(conds))

# Time window constraints:
# 1. In Copenhagen (city index 0) you must spend 5 days and meet your friend between day 11 and 15.
for i in range(10):
    # If segment i is Copenhagen then its stay [S, S+4] must intersect [11,15].
    s.add(Implies(seg[i] == 0, And(S_vars[i] <= 15, S_vars[i] + durations["Copenhagen"] - 1 >= 11)))

# 2. In Naples (city index 3) you plan to stay 4 days and visit relatives between day 5 and 8.
for i in range(10):
    s.add(Implies(seg[i] == 3, And(S_vars[i] <= 8, S_vars[i] + durations["Naples"] - 1 >= 5)))

# 3. In Athens (city index 6) you plan to stay 4 days and attend a workshop between day 8 and 11.
for i in range(10):
    s.add(Implies(seg[i] == 6, And(S_vars[i] <= 11, S_vars[i] + durations["Athens"] - 1 >= 8)))

# 4. In Mykonos (city index 2) you plan to stay 2 days and must be there for a conference on day 27 and 28.
for i in range(10):
    # The only way a stay of length 2 covers both days 27 and 28 is if it begins on day 27.
    s.add(Implies(seg[i] == 2, S_vars[i] == 27))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    # Build the itinerary segments: each is a triple (city, start_day, end_day).
    segments = []
    for i in range(10):
        city_index = m[seg[i]].as_long()
        city_name = cities[city_index]
        start_day = m[S_vars[i]].as_long()
        dur = durations[city_name]
        end_day = start_day + dur - 1
        segments.append((city_name, start_day, end_day))
    # For debugging, you might print the ordered segments:
    # for seg_info in segments:
    #     print(seg_info)

    # Build a day-to-cities mapping.
    # For each segment, every day from its start to its end belongs to that city.
    # When a flight occurs (i.e. the overlap day), two segments contribute.
    day_mapping = {day: [] for day in range(1, 29)}
    for (city, start_day, end_day) in segments:
        for day in range(start_day, end_day + 1):
            day_mapping[day].append(city)

    # Build the itinerary as a list of mappings; each mapping covers one day.
    itinerary = []
    for day in range(1, 29):
        # Each day, list the city (or cities, if flying that day) you are in.
        itinerary.append({"day": day, "place": day_mapping[day]})
    
    # Output the JSON dictionary with the key "itinerary"
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")