from z3 import *
import json

# We label the cities with integers:
# 0: Geneva, 1: Paris, 2: Oslo, 3: Porto, 4: Reykjavik
city_names = {0: "Geneva", 1: "Paris", 2: "Oslo", 3: "Porto", 4: "Reykjavik"}
# Required “days‐in‐city” (note that flight days are counted in both the city you leave and the city you arrive)
durations = {0: 7, 1: 6, 2: 5, 3: 7, 4: 2}

# Allowed direct flights – note flights are bidirectional.
# The provided pairs are:
# • Paris – Oslo       (1,2)
# • Geneva – Oslo      (0,2)
# • Porto – Paris      (3,1)
# • Geneva – Paris     (0,1)
# • Geneva – Porto     (0,3)
# • Paris – Reykjavik  (1,4)
# • Reykjavik – Oslo   (4,2)
# • Porto – Oslo       (3,2)
def allowed_pair(a, b):
    return Or(
        # Geneva - Paris
        And(a == 0, b == 1), And(a == 1, b == 0),
        # Geneva - Oslo
        And(a == 0, b == 2), And(a == 2, b == 0),
        # Geneva - Porto
        And(a == 0, b == 3), And(a == 3, b == 0),
        # Paris - Oslo
        And(a == 1, b == 2), And(a == 2, b == 1),
        # Paris - Reykjavik
        And(a == 1, b == 4), And(a == 4, b == 1),
        # Porto - Oslo
        And(a == 3, b == 2), And(a == 2, b == 3),
        # Porto - Paris (from “Porto and Paris”)
        And(a == 3, b == 1), And(a == 1, b == 3),
        # Reykjavik - Oslo (from “Reykjavik and Oslo”)
        And(a == 4, b == 2), And(a == 2, b == 4)
    )

s = Solver()

# We plan to visit 5 cities (one segment per city).
# The order matters and a “flight” (direct jump) happens at the boundary between segments.
# Because the flight day counts for both cities, the total day count is:
#    (sum of city-days) – (number of flights) = 27 – 4 = 23.
#
# We represent the itinerary as 5 segments.
# For each segment i, we have:
#  • seg_i: the city visited in that segment (an integer between 0 and 4)
#  • s_i: the start day for that segment.
#
# The segment i covers days [s_i, s_i + duration(seg_i) – 1].
# And for i>0 the start day is exactly the day when the previous segment ends:
#   s[i] == s[i-1] + duration(seg[i-1]) – 1.
#
# Also, note the extra constraints:
#  • The conference in Geneva must be attended on day 1 and day 7.
#    (So day 1 and day 7 must have Geneva in their “list of cities”.)
#  • You plan to visit relatives in Oslo sometime between day 19 and day 23,
#    so at least one day in Oslo must fall between 19 and 23.
#  • Additionally, the fixed durations are:
#         Geneva: 7, Paris: 6, Oslo: 5, Porto: 7, Reykjavik: 2.
#

# Create an array for the 5 segments (their city assignments)
segments = [Int(f"seg_{i}") for i in range(5)]
for seg in segments:
    s.add(Or([seg == c for c in city_names.keys()]))
# They must be distinct (visit each city exactly once)
s.add(Distinct(segments))
# The first segment must be Geneva so that day 1 is Geneva (conference day 1)
s.add(segments[0] == 0)

# Create an array for the start days of each segment.
start_days = [Int(f"s_{i}") for i in range(5)]
s.add(start_days[0] == 1)

# For each segment, the “duration” depends on the city.
def seg_duration(seg):
    # Use nested If’s to choose the required number of days.
    return If(seg == 0, durations[0],
           If(seg == 1, durations[1],
           If(seg == 2, durations[2],
           If(seg == 3, durations[3],
              durations[4]))))

# Impose that segments occur consecutively. For i>=1:
#   start_days[i] = start_days[i-1] + duration(seg[i-1]) – 1
for i in range(1, 5):
    s.add(start_days[i] == start_days[i-1] + seg_duration(segments[i-1]) - 1)

# The last segment must finish on day 23.
# That is: start_days[4] + duration(seg_4) – 1 == 23.
s.add(start_days[4] + seg_duration(segments[4]) - 1 == 23)

# Flight connectivity: for every consecutive segments i and i+1, the two cities must have a direct flight.
for i in range(4):
    s.add(allowed_pair(segments[i], segments[i+1]))

# Additional constraint for Oslo (city 2): if any segment is Oslo, then its visit interval
# [s, s + 5 – 1] must have at least one day between day 19 and day 23.
# It is enough to demand that the Oslo segment’s end day is not before day 19.
for i in range(5):
    s.add(Implies(segments[i] == 2, start_days[i] + durations[2] - 1 >= 19))

# (The conference on day 1 and day 7 is automatically met because segment 0 is Geneva,
# and Geneva covers days 1 ... 7.)

if s.check() == sat:
    m = s.model()
    # Retrieve the segment assignment and start day for each segment.
    # Compute each segment’s end day: end = start + duration – 1.
    itinerary_segments = []
    for i in range(5):
        city_val = m.evaluate(segments[i]).as_long()
        start_val = m.evaluate(start_days[i]).as_long()
        d_val = durations[city_val]
        end_val = start_val + d_val - 1
        itinerary_segments.append((city_val, start_val, end_val))
    # For clarity, here is one possible solution:
    #   Segment 0: Geneva (days 1 to 7)
    #   Segment 1: Paris   (days 7 to 12)
    #   Segment 2: Porto   (days 12 to 18)
    #   Segment 3: Oslo    (days 18 to 22)
    #   Segment 4: Reykjavik (days 22 to 23)
    #
    # Now, build the day-by-day itinerary.
    # On every day d from 1 to 23, we list all cities that have d in their interval.
    # (Note that when flying, e.g. on day 7, you are in both Geneva and Paris.)
    day_to_cities = {day: [] for day in range(1, 24)}
    for (city, start_day, end_day) in itinerary_segments:
        for day in range(start_day, end_day + 1):
            cname = city_names[city]
            if cname not in day_to_cities[day]:
                day_to_cities[day].append(cname)
                
    # Build a list of day-to-place mappings
    itinerary_list = []
    for day in range(1, 24):
        itinerary_list.append({"day": day, "places": day_to_cities[day]})
    
    output = {"itinerary": itinerary_list}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")