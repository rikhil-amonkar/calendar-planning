from z3 import *
import json

# We have 5 cities with fixed durations:
#   Riga:      duration 2 days
#   Istanbul:  duration 6 days
#   Krakow:    duration 7 days
#   Warsaw:    duration 3 days
#   Reykjavik: duration 7 days
#
# We also have two “event” constraints:
#  • Meet a friend in Riga between day 1 and day 2. 
#    → Whichever segment is in Riga must start no later than day 2.
#  • Wedding in Istanbul between day 2 and day 7.
#    → Whichever segment is in Istanbul must start by day 7 so that at least day 7 falls in its window.
#
# The travel uses only direct (undirected) flights.
# The allowed direct flight connections (in both directions) are:
#   - Istanbul <-> Krakow
#   - Warsaw <-> Reykjavik
#   - Istanbul <-> Warsaw
#   - Riga <-> Istanbul
#   - Krakow <-> Warsaw
#   - Riga <-> Warsaw
#
# The idea is that the trip is made of 5 segments (one per city).
# If you fly on the day the segment ends / next begins, that day “counts” for both cities.
# So the effective sum of days is:
#    sum(durations) - (number_of_flights)
# We have 5 cities so 4 flight days, and indeed: 2+6+7+3+7 = 25, minus 4 = 21 total calendar days.
#
# We encode:
#   - An array c[0..4] of integers representing the order in which the cities are visited.
#     We map: 0: Riga, 1: Istanbul, 2: Krakow, 3: Warsaw, 4: Reykjavik.
#   - An array s[0..4] of start days for the corresponding segments.
#     In each segment i the traveler is in city c[i] from day s[i] to day s[i] + (duration[c[i]] - 1).
#   - The flight day condition is enforced by requiring that for i >= 1,
#         s[i] = s[i-1] + (duration[c[i-1]] - 1).
#     (Because the last day of city i-1 is the first day of city i.)
#   - The overall trip must finish on day 21.
#
# We also add the event and connectivity constraints.
#
# Define the duration for each city by index.
durations = [2, 6, 7, 3, 7]  # indices: 0:Riga, 1:Istanbul, 2:Krakow, 3:Warsaw, 4:Reykjavik

# Allowed direct flight neighbors for each city (using our indices):
neighbors = {
    0: [1, 3],    # Riga connects to Istanbul and Warsaw.
    1: [0, 2, 3], # Istanbul connects to Riga, Krakow, Warsaw.
    2: [1, 3],    # Krakow connects to Istanbul and Warsaw.
    3: [0, 1, 2, 4],  # Warsaw connects to Riga, Istanbul, Krakow, Reykjavik.
    4: [3]        # Reykjavik connects only to Warsaw.
}

# Create a Z3 solver.
solver = Solver()

# Create 5 integer variables for the city order (each in 0..4)
c = [Int(f"c_{i}") for i in range(5)]
for ci in c:
    solver.add(And(ci >= 0, ci <= 4))
solver.add(Distinct(c))

# Create 5 integer variables for the start day of each segment.
s = [Int(f"s_{i}") for i in range(5)]
for si in s:
    solver.add(si >= 1)  # start days are at least 1

# The first segment must start on day 1.
solver.add(s[0] == 1)

# For each segment i, the segment lasts duration d = durations[c[i]]
# and the next segment starts on the last day of this one (which is double–counted).
for i in range(4):
    # s[i+1] = s[i] + (duration of city c[i]) - 1
    # Using an If-then-else over the five possible cities.
    solver.add(
        s[i+1] == s[i] + 
        (If(c[i]==0, durations[0],
         If(c[i]==1, durations[1],
         If(c[i]==2, durations[2],
         If(c[i]==3, durations[3],
         durations[4])))) - 1
    )

# The last segment's end day must equal 21.
# That is: s[4] + (duration for city c[4]) - 1 == 21.
solver.add(
    s[4] + (If(c[4]==0, durations[0],
            If(c[4]==1, durations[1],
            If(c[4]==2, durations[2],
            If(c[4]==3, durations[3],
               durations[4])))) - 1 == 21
)

# EVENT CONSTRAINTS:
# 1. Friend meeting in Riga between day1 and day2:
#    If a segment is in Riga (city index 0), then its time interval must cover day1 or day2.
#    Since the segment spans s[i] to s[i] + durations[0] - 1 and durations[0] is 2,
#    we can require that the segment start is <=2.
for i in range(5):
    solver.add( If(c[i] == 0, s[i] <= 2, True) )

# 2. Wedding in Istanbul between day2 and day7:
#    If a segment is in Istanbul (city index 1), then it must cover at least one day in [2,7].
#    Here it suffices to require that the segment starts on or before day 7.
for i in range(5):
    solver.add( If(c[i] == 1, s[i] <= 7, True) )

# FLIGHT CONNECTIVITY:
# For each consecutive pair of segments, the cities must be directly connected.
for i in range(4):
    # Build the constraint that (c[i], c[i+1]) is an allowed connection.
    # We do this by checking, for each possible value of c[i], that c[i+1] is one of its neighbors.
    conds = []
    # For city 0 (Riga): next city must be in [1, 3].
    conds.append(And(c[i] == 0, Or(c[i+1] == 1, c[i+1] == 3)))
    # For city 1 (Istanbul): next city must be in [0, 2, 3].
    conds.append(And(c[i] == 1, Or(c[i+1] == 0, c[i+1] == 2, c[i+1] == 3)))
    # For city 2 (Krakow): next city must be in [1, 3].
    conds.append(And(c[i] == 2, Or(c[i+1] == 1, c[i+1] == 3)))
    # For city 3 (Warsaw): next city must be in [0, 1, 2, 4].
    conds.append(And(c[i] == 3, Or(c[i+1] == 0, c[i+1] == 1, c[i+1] == 2, c[i+1] == 4)))
    # For city 4 (Reykjavik): next city must be [3].
    conds.append(And(c[i] == 4, c[i+1] == 3))
    solver.add(Or(*conds))

if solver.check() == sat:
    model = solver.model()
    # For easier reference build a mapping of city indices to names.
    city_names = {0: "Riga", 1: "Istanbul", 2: "Krakow", 3: "Warsaw", 4: "Reykjavik"}
    
    # Get the order and start days according to the model.
    order = [model.evaluate(c[i]).as_long() for i in range(5)]
    start_days = [model.evaluate(s[i]).as_long() for i in range(5)]
    
    # Compute the segment intervals.
    segments = []
    for i in range(5):
        city_idx = order[i]
        dur = durations[city_idx]
        seg_start = start_days[i]
        seg_end = seg_start + dur - 1
        segments.append({
            "city": city_names[city_idx],
            "start": seg_start,
            "end": seg_end
        })
    
    # Now, construct the daily itinerary.
    # On any day d, if d falls in a segment's interval, then the traveler is considered to be in that city.
    itinerary = []
    for day in range(1, 22):  # days 1 to 21
        day_cities = []
        for seg in segments:
            if seg["start"] <= day <= seg["end"]:
                day_cities.append(seg["city"])
        # If the day has exactly one city, output it as a string; if two (a flight day), output the list.
        if len(day_cities) == 1:
            entry = {"day": day, "city": day_cities[0]}
        else:
            entry = {"day": day, "city": day_cities}
        itinerary.append(entry)
    
    # Prepare final JSON output.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")