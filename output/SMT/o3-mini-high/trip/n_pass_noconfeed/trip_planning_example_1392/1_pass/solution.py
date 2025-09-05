from z3 import *
import json

# Define cities and their required durations
cities = {
    0: "Naples",
    1: "Valencia",
    2: "Stuttgart",
    3: "Split",
    4: "Venice",
    5: "Amsterdam",
    6: "Nice",
    7: "Barcelona",
    8: "Porto"
}
durations = {
    0: 3,  # Naples
    1: 5,  # Valencia
    2: 2,  # Stuttgart
    3: 5,  # Split
    4: 5,  # Venice
    5: 4,  # Amsterdam
    6: 2,  # Nice
    7: 2,  # Barcelona
    8: 4   # Porto
}

# Allowed direct flight pairs (unordered)
allowed_pairs = [
    (0, 1),  # Naples - Valencia
    (0, 2),  # Naples - Stuttgart
    (0, 3),  # Naples - Split
    (0, 4),  # Naples - Venice
    (0, 5),  # Naples - Amsterdam
    (0, 6),  # Naples - Nice
    (0, 7),  # Naples - Barcelona
    (1, 2),  # Valencia - Stuttgart
    (1, 5),  # Valencia - Amsterdam
    (1, 7),  # Valencia - Barcelona
    (1, 8),  # Valencia - Porto
    (2, 3),  # Stuttgart - Split
    (2, 4),  # Stuttgart - Venice
    (2, 5),  # Stuttgart - Amsterdam
    (2, 7),  # Stuttgart - Barcelona
    (2, 8),  # Stuttgart - Porto
    (3, 5),  # Split - Amsterdam
    (3, 7),  # Split - Barcelona
    (4, 5),  # Venice - Amsterdam
    (4, 6),  # Venice - Nice
    (4, 7),  # Venice - Barcelona
    (5, 6),  # Amsterdam - Nice
    (5, 7),  # Amsterdam - Barcelona
    (5, 8),  # Amsterdam - Porto
    (6, 7),  # Nice - Barcelona (from "Barcelona and Nice")
    (6, 8),  # Nice - Porto
    (7, 8)   # Barcelona - Porto
]

# There are 9 segments (one per city in the tour)
n_segments = 9

# Create SMT variables for the ordered tour:
# seg[i] indicates the city id visited in the i-th segment.
# start[i] indicates the starting day of the i-th segment.
seg = [Int(f"seg_{i}") for i in range(n_segments)]
start = [Int(f"start_{i}") for i in range(n_segments)]

s = Solver()

# Domain constraints
for i in range(n_segments):
    s.add(seg[i] >= 0, seg[i] <= 8)
    s.add(start[i] >= 1, start[i] <= 24)

# All cities must be visited exactly once
s.add(Distinct(seg))

# Helper: get the duration of a segment given the city variable.
def get_duration(city):
    return If(city == 0, 3,
           If(city == 1, 5,
           If(city == 2, 2,
           If(city == 3, 5,
           If(city == 4, 5,
           If(city == 5, 4,
           If(city == 6, 2,
           If(city == 7, 2,
           If(city == 8, 4, 0)))))))))

# Itinerary timing constraints:
# If you fly on the last day of a segment, you are also in the next city that day.
# So, if segment i has duration d_i then:
#   start[0] == 1
#   for i in 0..n_segments-2:  start[i+1] = start[i] + d_i - 1
#   and finish of last segment equals day 24.
s.add(start[0] == 1)
for i in range(n_segments - 1):
    s.add(start[i+1] == start[i] + get_duration(seg[i]) - 1)
s.add(start[n_segments - 1] + get_duration(seg[n_segments - 1]) - 1 == 24)

# Flight connectivity constraints:
# For each adjacent pair in the order, the two cities must have a direct flight.
for i in range(n_segments - 1):
    transition_allowed = []
    for (a, b) in allowed_pairs:
        # Either the pair is (a,b) or (b,a)
        transition_allowed.append(And(seg[i] == a, seg[i+1] == b))
        transition_allowed.append(And(seg[i] == b, seg[i+1] == a))
    s.add(Or(transition_allowed))

# Event constraints
for i in range(n_segments):
    # Venice conference: must attend on day 6 and day 10.
    # With a 5-day stay in Venice, the only possibility is to start on day 6.
    s.add(Implies(seg[i] == 4, start[i] == 6))
    
    # Barcelona workshop: must be attended between day 5 and day 6.
    # A 2-day stay in Barcelona that starts at day 4 (covering days 4-5),
    # or day 5 (covering days 5-6) or day 6 (covering days 6-7) works.
    s.add(Implies(seg[i] == 7, And(start[i] >= 4, start[i] <= 6)))
    
    # Naples friend meeting: must occur between day 18 and day 20.
    # A 3-day stay in Naples (days: start to start+2) must intersect [18,20]:
    # This is equivalent to: start[i] <= 20 and start[i] + 2 >= 18.
    s.add(Implies(seg[i] == 0, And(start[i] <= 20, start[i] + 2 >= 18)))
    
    # Nice friends tour: must occur between day 23 and day 24.
    # A 2-day stay in Nice (days: start, start+1) must intersect [23,24]:
    # This gives: start[i] + 1 >= 23 and start[i] <= 24.
    # Also to ensure a meeting day in the later part of the trip, enforce start[i] >= 22.
    s.add(Implies(seg[i] == 6, And(start[i] >= 22, start[i] <= 24, start[i] + 1 >= 23)))

# Find a solution and output the itinerary as JSON.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n_segments):
        city_id = m.evaluate(seg[i]).as_long()
        city_name = cities[city_id]
        seg_start = m.evaluate(start[i]).as_long()
        d = durations[city_id]
        seg_end = seg_start + d - 1
        itinerary.append({"day_range": f"Day {seg_start}-{seg_end}", "place": city_name})
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))