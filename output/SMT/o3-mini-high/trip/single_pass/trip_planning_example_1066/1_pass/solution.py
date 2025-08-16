from z3 import *
import json

# Define cities and their durations.
# We'll use the following mapping:
# 0: "Stuttgart", 1: "Brussels", 2: "Bucharest",
# 3: "Mykonos", 4: "Madrid", 5: "Helsinki",
# 6: "Split", 7: "London"
city_names = {
    0: "Stuttgart",
    1: "Brussels",
    2: "Bucharest",
    3: "Mykonos",
    4: "Madrid",
    5: "Helsinki",
    6: "Split",
    7: "London"
}
durations = {
    0: 4,  # Stuttgart: 4 days, also friend-meeting must occur in one of days 1-4
    1: 4,  # Brussels: 4 days
    2: 3,  # Bucharest: 3 days
    3: 2,  # Mykonos: 2 days
    4: 2,  # Madrid: 2 days (and the conference must be on days 20-21)
    5: 5,  # Helsinki: 5 days
    6: 3,  # Split: 3 days
    7: 5   # London: 5 days
}

# Allowed direct flights (bidirectional). Each tuple is (city_from, city_to).
allowed_edges = [
    (5, 7), (7, 5),       # Helsinki <-> London
    (6, 4), (4, 6),       # Split <-> Madrid
    (5, 4), (4, 5),       # Helsinki <-> Madrid
    (7, 4), (4, 7),       # London <-> Madrid
    (1, 7), (7, 1),       # Brussels <-> London
    (2, 7), (7, 2),       # Bucharest <-> London
    (1, 2), (2, 1),       # Brussels <-> Bucharest
    (2, 4), (4, 2),       # Bucharest <-> Madrid
    (6, 5), (5, 6),       # Split <-> Helsinki
    (3, 4), (4, 3),       # Mykonos <-> Madrid
    (0, 7), (7, 0),       # Stuttgart <-> London
    (5, 1), (1, 5),       # Helsinki <-> Brussels
    (1, 4), (4, 1),       # Brussels <-> Madrid
    (6, 7), (7, 6),       # Split <-> London
    (0, 6), (6, 0),       # Stuttgart <-> Split
    (7, 3), (3, 7)        # London <-> Mykonos
]

# There must be 8 segments (one per city) that cover 21 days in total.
# Because whenever you fly from one city to the next, the flight day is counted
# in both cities. Thus, if the segments have durations d1,...,d8 then:
#  Total days = d1 + ... + d8 - (number of transitions)
# and since  d1+...+d8 must equal 28 (given by the problem’s numbers),
# and there are 7 flights, we have 28-7 = 21 days.

# We will have:
#   itinerary[0..7]: an ordering (permutation) of the 8 cities.
#   s[0..7]: start days for each city segment.
# For segment i, the visit covers days: s[i] to s[i] + durations[city] - 1.
# The transitions between segments always overlap by one day, i.e.,
# if city A is followed by city B then s[i+1] = s[i] + duration(A) - 1

solver = Solver()

# Create 8 integer variables for the itinerary order.
# Each variable is in the domain 0..7, and they must be all different.
itinerary = [Int("city_%d" % i) for i in range(8)]
for c in itinerary:
    solver.add(And(c >= 0, c <= 7))
solver.add(Distinct(itinerary))

# Fix the endpoints:
# The friend meeting in Stuttgart must be early so we force Stuttgart (0) to occur first.
solver.add(itinerary[0] == 0)
# The conference in Madrid (4) must be on days 20-21 so force Madrid to be last.
solver.add(itinerary[7] == 4)

# Create 8 integer variables for the start day of each segment.
s = [Int("s_%d" % i) for i in range(8)]
# The trip starts on day 1.
solver.add(s[0] == 1)

# A helper to build an expression for the duration corresponding to a given city.
def duration_expr(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4],
           If(city_var == 5, durations[5],
           If(city_var == 6, durations[6],
              durations[7])))))))

# For segments 0..6, enforce that the next segment starts on:
#   s[i+1] = s[i] + duration(city[i]) - 1
for i in range(7):
    solver.add(s[i+1] == s[i] + duration_expr(itinerary[i]) - 1)

# Final day constraint: The last segment must finish on day 21.
solver.add(s[7] + duration_expr(itinerary[7]) - 1 == 21)

# Enforce that each flight (transition) is allowed.
for i in range(7):
    # For the pair (itinerary[i], itinerary[i+1]), it must be one of the allowed edges.
    allowed = []
    for (a, b) in allowed_edges:
        allowed.append(And(itinerary[i] == a, itinerary[i+1] == b))
    solver.add(Or(allowed))

# Enforce the friend meeting constraint:
# If a segment is Stuttgart (0), then at least one day of that segment is in days 1 to 4.
# Because the segment covers days s[i] to s[i]+duration-1, a sufficient condition is
# to require that if itinerary[i] == 0 then s[i] <= 4.
for i in range(8):
    solver.add(Or(itinerary[i] != 0, s[i] <= 4))

# Enforce the Madrid conference constraint:
# If a segment is Madrid (4) then it must start on day 20.
for i in range(8):
    solver.add(Or(itinerary[i] != 4, s[i] == 20))

# Check for a solution.
if solver.check() == sat:
    model = solver.model()

    # Recover the itinerary order and start days.
    segs = []
    for i in range(8):
        city = model[itinerary[i]].as_long()
        start_day = model[s[i]].as_long()
        dur = durations[city]
        end_day = start_day + dur - 1
        segs.append({
            "city": city_names[city],
            "start": start_day,
            "end": end_day,
            "duration": dur
        })

    # Now, build the day-to-cities mapping.
    # For each day 1..21, a day is covered by those segments for which:
    #    start <= day <= end.
    day_itinerary = []
    for d in range(1, 22):
        cities_today = []
        for seg in segs:
            if seg["start"] <= d <= seg["end"]:
                cities_today.append(seg["city"])
        day_itinerary.append({"day": d, "cities": cities_today})

    # Prepare the final JSON output.
    output = {"itinerary": day_itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")