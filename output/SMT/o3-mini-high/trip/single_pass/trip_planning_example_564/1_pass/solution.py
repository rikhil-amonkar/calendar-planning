from z3 import *

# Cities:
# 0: Istanbul (2 days)
# 1: Rome (3 days)
# 2: Seville (4 days)
# 3: Naples (7 days)
# 4: Santorini (4 days)
cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
durations = [2, 3, 4, 7, 4]  # index order per city above

# Allowed direct flight connections (bidirectional)
# (A,B) ∈ allowed if there is a direct flight between city A and city B.
allowed_pairs = [(0,1), (1,0),   # Istanbul <-> Rome 
                 (0,3), (3,0),   # Istanbul <-> Naples 
                 (1,4), (4,1),   # Rome <-> Santorini 
                 (2,1), (1,2),   # Seville <-> Rome 
                 (1,3), (3,1),   # Rome <-> Naples 
                 (3,4), (4,3)]   # Naples <-> Santorini 

s = Solver()

# We have 5 segments (one per city visit) whose order is a permutation of the 5 cities.
order = [Int("order_%d" % i) for i in range(5)]
for i in range(5):
    s.add(And(order[i] >= 0, order[i] <= 4))
s.add(Distinct(order))

# For every adjacent pair, require that there is a direct flight.
for i in range(4):
    s.add(Or([And(order[i] == a, order[i+1] == b) for (a, b) in allowed_pairs]))

# We now set up the “segment start day” variables.
# The idea is that if you spend d days in a city, and fly on the last day,
# then the segment interval is [start, start+d-1].  (The flight day is counted in both cities.)
seg_start = [Int("seg_start_%d" % i) for i in range(5)]
s.add(seg_start[0] == 1)  # first segment starts on day 1

# For each subsequent segment i>0, its start day equals the previous segment’s end day.
# (end day = seg_start + duration - 1)
for i in range(1, 5):
    # We “select” the duration corresponding to the city in the previous segment.
    d_prev = If(order[i-1] == 0, durations[0],
             If(order[i-1] == 1, durations[1],
             If(order[i-1] == 2, durations[2],
             If(order[i-1] == 3, durations[3],
                durations[4]))))
    s.add(seg_start[i] == seg_start[i-1] + d_prev - 1)

# The overall trip must run from day 1 to day 16.
# So the last segment’s end day is seg_start[4] + (its duration) - 1 = 16.
d_last = If(order[4] == 0, durations[0],
         If(order[4] == 1, durations[1],
         If(order[4] == 2, durations[2],
         If(order[4] == 3, durations[3],
            durations[4]))))
s.add(seg_start[4] + d_last - 1 == 16)

# Special scheduling constraints:
# (1) Istanbul: intended stay = 2 days.
#     In order to visit relatives “between day 6 and day 7” (i.e. one day in that interval)
#     the Istanbul visit (which covers [s, s+1]) must include day 6 or 7.
#     That is equivalent to requiring the segment’s start to be 5, 6 or 7.
for i in range(5):
    s.add(Implies(order[i] == 0, And(seg_start[i] >= 5, seg_start[i] <= 7)))

# (2) Santorini: intended stay = 4 days.
#     You need to attend a wedding in Santorini between days 13 and 16.
#     For a 4-day visit [s, s+3] to cover that range, a sufficient condition is s ≥ 10.
for i in range(5):
    s.add(Implies(order[i] == 4, seg_start[i] >= 10))

if s.check() == sat:
    m = s.model()
    order_val = [m.evaluate(order[i]).as_long() for i in range(5)]
    seg_start_val = [m.evaluate(seg_start[i]).as_long() for i in range(5)]
    
    # Build a list of segments as tuples (city, start, end)
    segments = []
    for i in range(5):
        city_index = order_val[i]
        city_name = cities[city_index]
        seg_duration = durations[city_index]
        start_day = seg_start_val[i]
        end_day = start_day + seg_duration - 1
        segments.append((city_name, start_day, end_day))
    
    # Construct a day-by-day itinerary for days 1 to 16.
    # Note that when a flight occurs on a day, that day is part of both segments,
    # so we list both cities (joined with a slash) for that day.
    day_itinerary = []
    for d in range(1, 17):
        places = []
        for (city, start_day, end_day) in segments:
            if d >= start_day and d <= end_day:
                places.append(city)
        # If more than one city appears on the same day (flight day), join them with "/"
        # Otherwise, just output the unique city.
        if len(places) == 1:
            city_str = places[0]
        else:
            # Remove duplicates (should not occur, but just in case)
            unique = []
            for item in places:
                if item not in unique:
                    unique.append(item)
            city_str = "/".join(unique)
        day_itinerary.append({"day": d, "city": city_str})
    
    # Create the final JSON output.
    import json
    output = {"itinerary": day_itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")