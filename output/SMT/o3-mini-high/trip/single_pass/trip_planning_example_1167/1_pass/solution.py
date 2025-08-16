from z3 import *
import json

# Create a Z3 solver instance.
solver = Solver()

# We have eight segments (one per city in our trip).
# Define two arrays of Z3 integer variables:
#   seg[i] will be the “city code” chosen at segment i.
#   start[i] will be the starting day (in 1..21) for that segment.
seg = [Int(f"seg_{i}") for i in range(8)]
start = [Int(f"start_{i}") for i in range(8)]

# We assign codes to cities as follows:
#  0: Dublin, 1: Krakow, 2: Istanbul, 3: Venice,
#  4: Naples, 5: Brussels, 6: Mykonos, 7: Frankfurt
city_names = ["Dublin", "Krakow", "Istanbul", "Venice",
              "Naples", "Brussels", "Mykonos", "Frankfurt"]

# Define a function mapping a city code to its required number of days.
# (Remember: the overlap in flight days is handled by our recurrence.)
def dur(city):
    return If(city == 0, 5,   # Dublin: 5 days
           If(city == 1, 4,   # Krakow: 4 days
           If(city == 2, 3,   # Istanbul: 3 days
           If(city == 3, 3,   # Venice: 3 days
           If(city == 4, 4,   # Naples: 4 days
           If(city == 5, 2,   # Brussels: 2 days
           If(city == 6, 4,   # Mykonos: 4 days
           If(city == 7, 3,  0))))))))

# Each seg[i] is an integer in 0..7 corresponding to one of the eight cities.
for i in range(8):
    solver.add(seg[i] >= 0, seg[i] <= 7)
    
# All cities must be different.
solver.add(Distinct(seg))

# Each segment’s start day is between 1 and 21.
for i in range(8):
    solver.add(start[i] >= 1, start[i] <= 21)
    
# The trip must start on day 1.
solver.add(start[0] == 1)

# For each segment i, the “end day” is start[i] + (duration for that city) – 1.
# Moreover, the next segment begins on the same day as the previous segment’s end.
for i in range(7):
    solver.add(start[i+1] == start[i] + dur(seg[i]) - 1)
    
# The last segment must end exactly on day 21.
solver.add(start[7] + dur(seg[7]) - 1 == 21)

# ------------------------------------------------------------------------
# Add the additional (side) constraints:
#
# 1. Dublin’s show: If a segment is Dublin (code 0) then it must run exactly from day 11 to 15.
for i in range(8):
    solver.add(Implies(seg[i] == 0, start[i] == 11))

# 2. Mykonos relatives: must be visited between day 1 and 4.
# (For simplicity we require that if a segment is Mykonos, then its start day is ≤ 4.)
for i in range(8):
    solver.add(Implies(seg[i] == 6, start[i] <= 4))

# 3. Istanbul friend meeting between day 9 and 11:
# The Istanbul segment (3 days long) must “touch” the interval [9,11].
# That is, start[i] must be ≤ 11 and start[i]+2 ≥ 9  (i.e. start[i] ≥ 7).
for i in range(8):
    solver.add(Implies(seg[i] == 2, And(start[i] >= 7, start[i] <= 11)))

# 4. Frankfurt tour with friends between day 15 and 17:
# The Frankfurt segment (3 days) must intersect [15,17], so we require start[i] ≥ 13 and ≤ 17.
for i in range(8):
    solver.add(Implies(seg[i] == 7, And(start[i] >= 13, start[i] <= 17)))

# ------------------------------------------------------------------------
# Now we add the direct–flight constraints.
# (If you fly on day X from city A to city B then A and B must be directly connected.
#  In our encoding these constraints are applied to consecutive segments.)
#
# We list all allowed pairs (both directions) according to the given list:
allowed_pairs = [
    (0, 5), (5, 0),       # Dublin – Brussels
    (6, 4), (4, 6),       # Mykonos – Naples
    (3, 2), (2, 3),       # Venice – Istanbul
    (7, 1), (1, 7),       # Frankfurt – Krakow
    (4, 0), (0, 4),       # Naples – Dublin
    (1, 5), (5, 1),       # Krakow – Brussels
    (4, 2), (2, 4),       # Naples – Istanbul
    (4, 5), (5, 4),       # Naples – Brussels
    (2, 7), (7, 2),       # Istanbul – Frankfurt
    (5, 7), (7, 5),       # Brussels – Frankfurt (given as “from Brussels to Frankfurt”)
    (2, 1), (1, 2),       # Istanbul – Krakow
    (2, 5), (5, 2),       # Istanbul – Brussels
    (3, 7), (7, 3),       # Venice – Frankfurt
    (4, 7), (7, 4),       # Naples – Frankfurt
    (0, 1), (1, 0),       # Dublin – Krakow
    (3, 5), (5, 3),       # Venice – Brussels
    (4, 3), (3, 4),       # Naples – Venice
    (2, 0), (0, 2),       # Istanbul – Dublin
    (3, 0), (0, 3),       # Venice – Dublin
    (0, 7), (7, 0)        # Dublin – Frankfurt
]

# For each consecutive pair of segments, require that (seg[i], seg[i+1]) is an allowed flight.
for i in range(7):
    solver.add(Or([And(seg[i] == a, seg[i+1] == b) for (a, b) in allowed_pairs]))

# ------------------------------------------------------------------------
# Solve and then output a JSON itinerary.
if solver.check() == sat:
    model = solver.model()
    itinerary_segments = []
    # For each segment compute the city, starting day, and ending day (remember: end = start + duration – 1).
    for i in range(8):
        city_code = model[seg[i]].as_long()
        s_day = model[start[i]].as_long()
        # Compute duration (we use the same mapping as in dur) 
        if city_code == 0:  d_val = 5
        elif city_code == 1: d_val = 4
        elif city_code == 2: d_val = 3
        elif city_code == 3: d_val = 3
        elif city_code == 4: d_val = 4
        elif city_code == 5: d_val = 2
        elif city_code == 6: d_val = 4
        elif city_code == 7: d_val = 3
        e_day = s_day + d_val - 1
        itinerary_segments.append({
            "city": city_names[city_code],
            "start_day": s_day,
            "end_day": e_day
        })
    
    # (They are already in order from day 1 to 21.)
    # We then produce a “list of day–place mappings” by printing each segment as:
    # "Day X–Y: City"
    itinerary_output = []
    for seg_info in itinerary_segments:
        itinerary_output.append(f"Day {seg_info['start_day']}-{seg_info['end_day']}: {seg_info['city']}")
    
    output = {"itinerary": itinerary_output}
    print(json.dumps(output, indent=4))
else:
    print("No solution found")