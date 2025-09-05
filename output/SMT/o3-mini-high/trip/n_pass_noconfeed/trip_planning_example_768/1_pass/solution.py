from z3 import *
import json

def get_duration(city):
    # Duration for each city based on its ID:
    # 0: Mykonos = 4, 1: London = 2, 2: Copenhagen = 3, 3: Oslo = 5, 4: Tallinn = 4, 5: Nice = 3
    return If(city == 0, 4,
           If(city == 1, 2,
           If(city == 2, 3,
           If(city == 3, 5,
           If(city == 4, 4, 3)))))

# Allowed direct flights are bidirectional.
# For flights between the first 5 segments (cities among {0,1,2,3,4}), the allowed edges are:
# Mykonos (0) <-> London (1)
# London (1) <-> Copenhagen (2)
# London (1) <-> Oslo (3)
# Copenhagen (2) <-> Tallinn (4)
# Copenhagen (2) <-> Oslo (3)
# Oslo (3) <-> Tallinn (4)
allowed_internal = [
    (0, 1), (1, 0),
    (1, 2), (2, 1),
    (1, 3), (3, 1),
    (2, 4), (4, 2),
    (2, 3), (3, 2),
    (4, 3), (3, 4)
]
# For the flight from the 5th segment (index 4) to Nice (5), the allowed pairs are:
# Mykonos (0) -> Nice (5), London (1) -> Nice (5),
# Copenhagen (2) -> Nice (5), Oslo (3) -> Nice (5)
# This means that the city in segment 5 (index 4) must not be Tallinn (4).

# Create the solver
solver = Solver()

# We have 5 segments (indices 0 to 4) to order the cities among {0,1,2,3,4}.
s0, s1, s2, s3, s4 = Ints('s0 s1 s2 s3 s4')
segments = [s0, s1, s2, s3, s4]
# Each segment must be one of the cities {0,1,2,3,4}; Nice (5) is fixed as the 6th segment.
for s in segments:
    solver.add(s >= 0, s <= 4)
solver.add(Distinct(s0, s1, s2, s3, s4))

# Add flight constraints for consecutive segments (0..3)
for i in range(4):
    conds = []
    for (a, b) in allowed_internal:
        conds.append(And(segments[i] == a, segments[i+1] == b))
    solver.add(Or(conds))

# Flight from segment 5 (s4) to Nice (5) is allowed only when s4 is in {0,1,2,3}; Tallinn (4) is not allowed here.
solver.add(Or(s4 == 0, s4 == 1, s4 == 2, s4 == 3))

# Define the time intervals for each segment.
# We use the rule: if segment i covers days d_i to e_i then the "duration" (i.e. counted days) for that city is (e_i - d_i + 1).
# When flying between segments, the flight day is shared.
# Let segments 0 ... 4 correspond to our permutation cities, and segment 5 is fixed to Nice.
# We set:
#   d0 = 1
#   e0 = d0 + get_duration(s0) - 1
#   d1 = e0,   e1 = d1 + get_duration(s1) - 1
#   d2 = e1,   e2 = d2 + get_duration(s2) - 1
#   d3 = e2,   e3 = d3 + get_duration(s3) - 1
#   d4 = e3,   e4 = d4 + get_duration(s4) - 1
# For segment 5 (Nice), its duration is fixed (3 days) and we require:
#   d5 = e4,   e5 = d5 + 3 - 1, and e5 must equal 16.
d0 = Int('d0')
e0 = Int('e0')
d1 = Int('d1')
e1 = Int('e1')
d2 = Int('d2')
e2 = Int('e2')
d3 = Int('d3')
e3 = Int('e3')
d4 = Int('d4')
e4 = Int('e4')
d5 = Int('d5')
e5 = Int('e5')

solver.add(d0 == 1)
dur0 = get_duration(s0)
solver.add(e0 == d0 + dur0 - 1)

solver.add(d1 == e0)
dur1 = get_duration(s1)
solver.add(e1 == d1 + dur1 - 1)

solver.add(d2 == e1)
dur2 = get_duration(s2)
solver.add(e2 == d2 + dur2 - 1)

solver.add(d3 == e2)
dur3 = get_duration(s3)
solver.add(e3 == d3 + dur3 - 1)

solver.add(d4 == e3)
dur4 = get_duration(s4)
solver.add(e4 == d4 + dur4 - 1)

# For segment 5 (Nice), its duration is fixed at 3 days.
solver.add(d5 == e4)
solver.add(e5 == d5 + 3 - 1)
# Total trip must last 16 days; hence, e5 == 16.
solver.add(e5 == 16)
# This forces e4 (the end of segment 5 from the first five cities) to be 14,
# so the Nice segment covers exactly Day 14-16 (thus meeting the conference days requirement).

# Meeting friend in Oslo: if Oslo (city 3) is visited in any of segments 0-4,
# then its interval [d_i, e_i] must include at least one day between Day 10 and Day 14.
# We enforce: if segment i is Oslo then d_i <= 14 and e_i >= 10.
solver.add(Implies(s0 == 3, And(d0 <= 14, e0 >= 10)))
solver.add(Implies(s1 == 3, And(d1 <= 14, e1 >= 10)))
solver.add(Implies(s2 == 3, And(d2 <= 14, e2 >= 10)))
solver.add(Implies(s3 == 3, And(d3 <= 14, e3 >= 10)))
solver.add(Implies(s4 == 3, And(d4 <= 14, e4 >= 10)))

# Solve the constraints
if solver.check() == sat:
    m = solver.model()
    # Build the ordered list of cities.
    # Segments 0 to 4 come from the permutation; segment 5 is fixed to Nice (5).
    seg_order = [m[s0].as_long(), m[s1].as_long(), m[s2].as_long(), m[s3].as_long(), m[s4].as_long(), 5]
    # Map city IDs to names.
    city_names = {
        0: "Mykonos",
        1: "London",
        2: "Copenhagen",
        3: "Oslo",
        4: "Tallinn",
        5: "Nice"
    }
    # Extract the day intervals from the model.
    d0_val = m.evaluate(d0).as_long()
    e0_val = m.evaluate(e0).as_long()
    d1_val = m.evaluate(d1).as_long()
    e1_val = m.evaluate(e1).as_long()
    d2_val = m.evaluate(d2).as_long()
    e2_val = m.evaluate(e2).as_long()
    d3_val = m.evaluate(d3).as_long()
    e3_val = m.evaluate(e3).as_long()
    d4_val = m.evaluate(d4).as_long()
    e4_val = m.evaluate(e4).as_long()
    # Segment 5 (Nice) is fixed to Day 14-16.
    itinerary = []
    itinerary.append({"day_range": "Day {}-{}".format(d0_val, e0_val), "place": city_names[seg_order[0]]})
    itinerary.append({"day_range": "Day {}-{}".format(d1_val, e1_val), "place": city_names[seg_order[1]]})
    itinerary.append({"day_range": "Day {}-{}".format(d2_val, e2_val), "place": city_names[seg_order[2]]})
    itinerary.append({"day_range": "Day {}-{}".format(d3_val, e3_val), "place": city_names[seg_order[3]]})
    itinerary.append({"day_range": "Day {}-{}".format(d4_val, e4_val), "place": city_names[seg_order[4]]})
    itinerary.append({"day_range": "Day 14-16", "place": city_names[5]})
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))