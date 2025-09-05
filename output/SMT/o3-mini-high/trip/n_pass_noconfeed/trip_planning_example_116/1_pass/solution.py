from z3 import *
import json

# Input parameters
total_days = 18
required_durations = {"Split": 6, "London": 7, "Santorini": 7}
conference_days = [12, 18]

# Mapping for cities to integers: 0: Split, 1: London, 2: Santorini
city_names = {0: "Split", 1: "London", 2: "Santorini"}

# Allowed direct flights between cities (bidirectional).
# Allowed pairs: (Split, London) and (London, Santorini) in either direction.
def allowed_flight(city_a, city_b):
    return Or(And(city_a == 0, city_b == 1), 
              And(city_a == 1, city_b == 0),
              And(city_a == 1, city_b == 2), 
              And(city_a == 2, city_b == 1))

solver = Solver()

# Declare variables for city assignments for each segment
c1, c2, c3 = Ints('c1 c2 c3')
# Each c_i must be 0, 1, or 2
solver.add(And(c1 >= 0, c1 <= 2))
solver.add(And(c2 >= 0, c2 <= 2))
solver.add(And(c3 >= 0, c3 <= 2))
# Cities must be distinct
solver.add(Distinct(c1, c2, c3))

# Conference requirement: Must be in Santorini on day 18 
# (and later constraint ensures day 12 is also in Santorini via overlap)
solver.add(c3 == 2)

# Flight constraints: consecutive segments must be connected by a direct flight.
solver.add(allowed_flight(c1, c2))
solver.add(allowed_flight(c2, c3))

# Declare duration variables for each segment.
d1, d2, d3 = Ints('d1 d2 d3')

# Based on city, assign fixed duration limits:
# If city is Split (0) then duration=6, if London (1) then =7, if Santorini (2) then =7.
solver.add(If(c1 == 0, d1 == required_durations["Split"],
           If(c1 == 1, d1 == required_durations["London"], d1 == required_durations["Santorini"])))
solver.add(If(c2 == 0, d2 == required_durations["Split"],
           If(c2 == 1, d2 == required_durations["London"], d2 == required_durations["Santorini"])))
solver.add(If(c3 == 0, d3 == required_durations["Split"],
           If(c3 == 1, d3 == required_durations["London"], d3 == required_durations["Santorini"])))

# We have 2 flights which means 2 days get double counted.
# Total of segment durations must equal total_days + 2.
solver.add(d1 + d2 + d3 == total_days + 2)

# Define the segmentation boundaries.
# Let segment 1 be from s1 to e1, segment 2 from s2 to e2, and segment 3 from s3 to e3.
s1, e1 = Ints('s1 e1')
s2, e2 = Ints('s2 e2')
s3, e3 = Ints('s3 e3')

solver.add(s1 == 1)
solver.add(e1 == s1 + d1 - 1)
solver.add(s2 == e1)     # flight day: last day of seg1 == first day of seg2
solver.add(e2 == s2 + d2 - 1)
solver.add(s3 == e2)     # flight day: last day of seg2 == first day of seg3
solver.add(e3 == s3 + d3 - 1)
solver.add(e3 == total_days)

# Conference constraints: On each conference day, the traveler must be in Santorini.
# A day is "in" a segment if it is between its start and end (inclusive).
for conf_day in conference_days:
    solver.add(
        Or(
            And(s1 <= conf_day, conf_day <= e1, c1 == 2),
            And(s2 <= conf_day, conf_day <= e2, c2 == 2),
            And(s3 <= conf_day, conf_day <= e3, c3 == 2)
        )
    )

if solver.check() == sat:
    model = solver.model()
    # Retrieve the segment boundaries and cities
    seg1_start = model[s1].as_long()
    seg1_end = model[e1].as_long()
    seg2_start = model[s2].as_long()
    seg2_end = model[e2].as_long()
    seg3_start = model[s3].as_long()
    seg3_end = model[e3].as_long()
    
    city1 = city_names[model[c1].as_long()]
    city2 = city_names[model[c2].as_long()]
    city3 = city_names[model[c3].as_long()]
    
    itinerary = [
        {"day_range": f"Day {seg1_start}-{seg1_end}", "place": city1},
        {"day_range": f"Day {seg2_start}-{seg2_end}", "place": city2},
        {"day_range": f"Day {seg3_start}-{seg3_end}", "place": city3}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No valid itinerary found"}))