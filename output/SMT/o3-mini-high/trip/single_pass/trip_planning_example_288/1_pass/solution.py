from z3 import *
import json

# We assign an integer to each city:
# 0: Manchester    (7 days, wedding between day 1-7)
# 1: Madrid        (4 days)
# 2: Vienna        (2 days)
# 3: Stuttgart     (5 days, workshop between day 11-15)

# Pre‐defined durations for each city
durations = [7, 4, 2, 5]

# Helper: given a city code (as a Z3 Int) return its duration.
def duration(city):
    return If(city == 0, 7,
           If(city == 1, 4,
           If(city == 2, 2,
           5)))

# Helper: given a city code (an integer) return its name.
city_names = {0: "Manchester", 1: "Madrid", 2: "Vienna", 3: "Stuttgart"}

# Allowed direct flights are given by the following pairs (bidirectional):
# Manchester <-> Madrid, Manchester <-> Vienna, Manchester <-> Stuttgart,
# Madrid <-> Vienna, and Vienna <-> Stuttgart.
# Using our numbering:
#   Manchester = 0, Madrid = 1, Vienna = 2, Stuttgart = 3.
# So allowed ordered pairs (a,b) are:
#   (0,1), (0,2), (0,3),
#   (1,0), (1,2),
#   (2,0), (2,1), (2,3),
#   (3,0), (3,2).
def allowed_flight(a, b):
    return Or(And(a == 0, Or(b == 1, b == 2, b == 3)),
              And(a == 1, Or(b == 0, b == 2)),
              And(a == 2, Or(b == 0, b == 1, b == 3)),
              And(a == 3, Or(b == 0, b == 2)))

# Create a Z3 solver instance.
s = Solver()

# We have four segments (one per city visit) in a 15-day itinerary.
# Let p0, p1, p2, p3 be the permutation (order) of cities.
p0, p1, p2, p3 = Ints('p0 p1 p2 p3')
s.add(And(p0 >= 0, p0 <= 3))
s.add(And(p1 >= 0, p1 <= 3))
s.add(And(p2 >= 0, p2 <= 3))
s.add(And(p3 >= 0, p3 <= 3))
s.add(Distinct(p0, p1, p2, p3))

# We also determine the start day for each segment.
# The rule is: if you fly on a day from one segment to the next, that day is counted for both segments.
# Hence if a segment with duration d starts on day X, it occupies days X through X+d-1.
# And the next segment must start on the flight day: i.e. the next segment's start day equals (previous start day + d - 1).
s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
s.add(s0 == 1)  # The trip starts on day 1.
s.add(s1 == s0 + duration(p0) - 1)
s.add(s2 == s1 + duration(p1) - 1)
s.add(s3 == s2 + duration(p2) - 1)
# The last segment for city p3 runs from s3 through s3 + duration(p3) - 1.
s.add(s3 + duration(p3) - 1 == 15)

# Add event constraints:
# Wedding in Manchester (city 0) must occur between day 1 and day 7.
# This means that whichever segment is Manchester must have at least one day in the interval [1,7].
# Since each segment runs from its start day s to s + duration - 1, a sufficient constraint is:
#   if the segment's city is Manchester then its start day must be <= 7.
# (Because s is at least 1, so if s <= 7 then some day in that segment falls ≤ 7.)
for seg, s_seg in zip([p0, p1, p2, p3], [s0, s1, s2, s3]):
    s.add(Implies(seg == 0, s_seg <= 7))

# Workshop in Stuttgart (city 3) must occur between day 11 and day 15.
# For the segment with Stuttgart (duration 5) the days run from s to s+4.
# We need some overlap with [11,15]. A sufficient constraint is that s + 4 >= 11.
for seg, s_seg in zip([p0, p1, p2, p3], [s0, s1, s2, s3]):
    s.add(Implies(seg == 3, s_seg + 4 >= 11))

# Add direct flight connectivity constraints between consecutive segments.
s.add( allowed_flight(p0, p1) )
s.add( allowed_flight(p1, p2) )
s.add( allowed_flight(p2, p3) )

# Check for a solution.
if s.check() == sat:
    m = s.model()
    # Get the order and start days
    order = [m[p0].as_long(), m[p1].as_long(), m[p2].as_long(), m[p3].as_long()]
    starts = [m[s0].as_long(), m[s1].as_long(), m[s2].as_long(), m[s3].as_long()]
    segs = []
    for i in range(4):
        city_code = order[i]
        city = city_names[city_code]
        # Compute the duration using our durations list.
        d = durations[city_code]
        start_day = starts[i]
        end_day = start_day + d - 1
        segs.append({
            "city": city,
            "start_day": start_day,
            "end_day": end_day
        })
        
    # The itinerary segments overlap on flight days.
    # For example, if one segment ends on a day and the next segment starts that same day,
    # that day is counted for both cities.
    # Output a JSON dictionary with the itinerary.
    itinerary = {"itinerary": segs}
    print(json.dumps(itinerary, indent=4))
else:
    print("No solution found")