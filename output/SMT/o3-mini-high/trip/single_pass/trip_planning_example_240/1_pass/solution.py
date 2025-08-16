from z3 import *
import json

# City encoding
# 0: Prague, 1: Berlin, 2: Tallinn, 3: Stockholm
Prague, Berlin, Tallinn, Stockholm = 0, 1, 2, 3
city_names = {0: "Prague", 1: "Berlin", 2: "Tallinn", 3: "Stockholm"}

# Allowed direct flight connections (bidirectional pairs)
# As given: Berlin–Tallinn, Prague–Tallinn, Stockholm–Tallinn, Prague–Stockholm, Stockholm–Berlin
allowed_transitions = [
    (Berlin, Tallinn), (Tallinn, Berlin),
    (Prague, Tallinn), (Tallinn, Prague),
    (Stockholm, Tallinn), (Tallinn, Stockholm),
    (Prague, Stockholm), (Stockholm, Prague),
    (Stockholm, Berlin), (Berlin, Stockholm)
]

# We have 4 segments to cover 12 days.
# When flying between segments the flight day is counted twice.
n_segments = 4

# Create Z3 variables for each segment:
#   seg_city[i] is an integer representing the city on segment i.
#   seg_start[i] is the day when segment i starts.
#   seg_end[i] is the day when segment i ends.
seg_city = [Int(f"seg_city_{i}") for i in range(n_segments)]
seg_start = [Int(f"seg_start_{i}") for i in range(n_segments)]
seg_end   = [Int(f"seg_end_{i}")   for i in range(n_segments)]

s = Solver()

# Each segment’s city is between 0 and 3, and all four must be distinct.
for i in range(n_segments):
    s.add(And(seg_city[i] >= 0, seg_city[i] <= 3))
s.add(Distinct(seg_city))

# Define duration (number of days) to be spent in each city.
# The rule is: if flying on a day, that day counts in both the city you’re leaving and the city you arrive in.
# Thus if a city’s “stay” is planned for D days, then in our consecutive segments model the segment length is D.
def duration(city):
    return If(city == Prague, 2,
           If(city == Berlin,  3,
           If(Or(city == Tallinn, city == Stockholm), 5, 0))) 

# The itinerary spans days 1 to 12.
s.add(seg_start[0] == 1)  # The trip starts on day 1.
for i in range(n_segments):
    # The end day is determined by start day and the required duration.
    s.add(seg_end[i] == seg_start[i] + duration(seg_city[i]) - 1)
    s.add(seg_start[i] >= 1)
    s.add(seg_end[i] <= 12)
    
# Consecutive segments must "touch": the flight day is the end day of the previous segment and the start day of the next.
for i in range(1, n_segments):
    s.add(seg_start[i] == seg_end[i-1])
s.add(seg_end[n_segments - 1] == 12)  # The trip ends on day 12.

# Only direct flights are allowed between consecutive segments.
for i in range(n_segments - 1):
    # For the flight from segment i to segment i+1, the pair (seg_city[i], seg_city[i+1])
    # must be one of the allowed direct flight pairs.
    flight_options = []
    for (a, b) in allowed_transitions:
        flight_options.append(And(seg_city[i] == a, seg_city[i+1] == b))
    s.add(Or(flight_options))

# Constraint: You must attend a conference in Berlin on day 6 and day 8.
# A day d is “covered” by a segment i if seg_start[i] <= d <= seg_end[i].
# (Note that if d = seg_start[i] for i>0, then d is in both segment i-1 and segment i.)
for d in [6, 8]:
    day_has_berlin = []
    for i in range(n_segments):
        day_has_berlin.append(And(seg_start[i] <= d, d <= seg_end[i], seg_city[i] == Berlin))
    s.add(Or(day_has_berlin))

# Constraint: You plan to visit relatives in Tallinn between day 8 and day 12.
# This means that the segment in Tallinn must overlap the interval [8, 12].
for i in range(n_segments):
    s.add(Or(seg_city[i] != Tallinn,
             And(seg_start[i] <= 12, seg_end[i] >= 8)))

# Find a solution.
if s.check() == sat:
    m = s.model()
    # Reconstruct the day-by-day itinerary.
    # For each day d (1 to 12), determine which segments are active.
    itinerary = []
    for day in range(1, 13):
        cities_today = []
        for i in range(n_segments):
            start_val = m.eval(seg_start[i]).as_long()
            end_val = m.eval(seg_end[i]).as_long()
            # If the day falls in the range for a segment, add its city.
            if start_val <= day <= end_val:
                cities_today.append(city_names[m.eval(seg_city[i]).as_long()])
        # On flight days two segments contribute.
        itinerary.append({"day": day, "cities": cities_today})
    
    # Output the itinerary in JSON format.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")