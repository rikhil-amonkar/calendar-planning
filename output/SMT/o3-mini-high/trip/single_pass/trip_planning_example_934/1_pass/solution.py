from z3 import Solver, Int, If, And, Or, Implies, Distinct

# We have 7 cities with fixed required day‐counts (durations)
# and several appointment/event constraints.
#
# Cities (we assign an integer for each):
#   0: Brussels    (5 days) – must include at least one day between day 7 and day 11 (for the workshop)
#   1: Rome        (2 days) 
#   2: Dubrovnik   (3 days)
#   3: Geneva      (5 days)
#   4: Budapest    (2 days) – must include at least one day between day 16 and day 17 (meet friend)
#   5: Riga        (4 days) – must include at least one day between day 4 and day 7 (meet friends)
#   6: Valencia    (2 days)
#
# IMPORTANT: When flying from one city segment to the next,
# the flight day is “double‐counted” (it is included in both segments).
#
# The direct flight (edge) connections (with the one directed flight noted) are:
#   Brussels–Valencia      (bidirectional)
#   Rome–Valencia          (bidirectional)
#   Brussels–Geneva        (bidirectional)
#   Rome–Geneva            (bidirectional)
#   Dubrovnik–Geneva       (bidirectional)
#   Valencia–Geneva         (bidirectional)
#   Rome -> Riga            (only from Rome to Riga)
#   Geneva–Budapest        (bidirectional)
#   Riga–Brussels         (bidirectional)
#   Rome–Budapest          (bidirectional)
#   Rome–Brussels          (bidirectional)
#   Brussels–Budapest      (bidirectional)
#   Dubrovnik–Rome         (bidirectional)
#
# Since the total “visited‐days” (summing required days) is:
#   5 + 2 + 3 + 5 + 2 + 4 + 2 = 23
#
# and because every time we fly the flight day is double counted,
# with 7 city segments there are 6 overlaps so the itinerary length is
# 23 - 6 = 17 days.
#
# We now set up a Z3 model in which:
#   - "order[i]" (for i=0,…,6) is the city visited in segment i.
#   - Each segment i has a start day S_i.
#   - For each segment i, if the city requires d days then the segment spans from day S_i to day S_i + d - 1.
#   - By design S_0 = 1 and for every consecutive pair the next segment’s start is the previous segment’s end.
#   - The last segment ends on day 17.
#   - For every consecutive pair of segments the flight (i.e. the transition) must be allowed.
#   - We also add the appointment constraints for Brussels, Riga and Budapest.

# Mapping from city id to duration (days) required:
durations = {
    0: 5,  # Brussels
    1: 2,  # Rome
    2: 3,  # Dubrovnik
    3: 5,  # Geneva
    4: 2,  # Budapest
    5: 4,  # Riga
    6: 2   # Valencia
}

# Mapping from city id to name
city_names = {
    0: "Brussels",
    1: "Rome",
    2: "Dubrovnik",
    3: "Geneva",
    4: "Budapest",
    5: "Riga",
    6: "Valencia"
}

# Allowed direct flight transitions (as (from, to)); note that all pairs are bidirectional except:
# - Flight from Rome to Riga is only allowed in that order.
allowed_pairs = [
    (0, 6), (6, 0),            # Brussels <-> Valencia
    (1, 6), (6, 1),            # Rome <-> Valencia
    (0, 3), (3, 0),            # Brussels <-> Geneva
    (1, 3), (3, 1),            # Rome <-> Geneva
    (2, 3), (3, 2),            # Dubrovnik <-> Geneva
    (6, 3), (3, 6),            # Valencia <-> Geneva
    (1, 5),                  # Rome -> Riga (only allowed in this direction)
    (3, 4), (4, 3),            # Geneva <-> Budapest
    (5, 0), (0, 5),            # Riga <-> Brussels
    (1, 4), (4, 1),            # Rome <-> Budapest
    (1, 0), (0, 1),            # Rome <-> Brussels
    (0, 4), (4, 0),            # Brussels <-> Budapest
    (2, 1), (1, 2)             # Dubrovnik <-> Rome
]

# Create the Z3 solver
s = Solver()

# Create 7 integer variables for the order (permutation) of the seven cities.
order = [Int(f"order_{i}") for i in range(7)]
for i in range(7):
    s.add(order[i] >= 0, order[i] < 7)
s.add(Distinct(order))

# Create 7 integer variables for the start day S_i for each segment.
S_vars = [Int(f"S_{i}") for i in range(7)]
s.add(S_vars[0] == 1)  # The itinerary starts on day 1.

# Because the duration depends on the city chosen, we define a helper function:
def get_duration(city_var):
    # city_var is an expression (could be one of our order[i] variables);
    # We use nested If’s to choose the correct duration.
    return If(city_var == 0, 5,
           If(city_var == 1, 2,
           If(city_var == 2, 3,
           If(city_var == 3, 5,
           If(city_var == 4, 2,
           If(city_var == 5, 4,
           If(city_var == 6, 2, 0)))))))

# For each consecutive segment, the flight day is double counted. Hence, if the city in segment i requires d days,
# then segment i spans from S_vars[i] to S_vars[i] + d - 1 and the next segment starts on the same day as the end of segment i.
for i in range(6):
    d_i = get_duration(order[i])
    s.add(S_vars[i+1] == S_vars[i] + d_i - 1)

# The last segment must end on day 17.
last_duration = get_duration(order[6])
s.add(S_vars[6] + last_duration - 1 == 17)

# Add flight connection constraints for consecutive segments.
for i in range(6):
    a = order[i]
    b = order[i+1]
    # For each transition we require that the (a, b) pair is one of the allowed pairs.
    allowed_expr = [And(a == x, b == y) for (x, y) in allowed_pairs]
    s.add(Or(allowed_expr))

# Add the appointment constraints:
# 1. Brussels (city 0) must be visited long enough so that at least one day from day 7 to 11 falls inside its segment.
#    Since Brussels requires 5 days, if its segment starts at S then it covers days S..S+4.
#    A sufficient constraint is: S <= 11 and S+4 >= 7.
for i in range(7):
    s.add(Implies(order[i] == 0, And(S_vars[i] <= 11, S_vars[i] + 4 >= 7)))
    
# 2. Riga (city 5) must include at least one day between day 4 and day 7.
#    Riga spans S..S+3; so we force S <= 7 and S+3 >= 4.
for i in range(7):
    s.add(Implies(order[i] == 5, And(S_vars[i] <= 7, S_vars[i] + 3 >= 4)))
    
# 3. Budapest (city 4) must include at least one day between day 16 and day 17.
#    Budapest spans S..S+1; so we require S <= 17 and S+1 >= 16.
for i in range(7):
    s.add(Implies(order[i] == 4, And(S_vars[i] <= 17, S_vars[i] + 1 >= 16)))

# Now try to solve.
if s.check().r == 1:  # sat
    m = s.model()
    sol_order = [m.evaluate(order[i]).as_long() for i in range(7)]
    sol_S = [m.evaluate(S_vars[i]).as_long() for i in range(7)]
    
    # For clarity, compute each segment: the city, its start day, and its end day.
    segments = []
    for i in range(7):
        city = sol_order[i]
        dur = durations[city]  # fixed number of days for that city
        start_day = sol_S[i]
        end_day = start_day + dur - 1
        segments.append((city, start_day, end_day))
    
    # Build the overall itinerary day by day.
    # Remember: if a flight occurs on day X, that day is part of both the previous and next city intervals.
    itinerary_by_day = {}
    for day in range(1, 18):  # days 1 to 17
        itinerary_by_day[day] = []
        for (city, start, end) in segments:
            if day >= start and day <= end:
                itinerary_by_day[day].append(city_names[city])
    
    # Create a list of day->cities mappings.
    itinerary_list = []
    for day in range(1, 18):
        itinerary_list.append({"day": day, "cities": itinerary_by_day[day]})
    
    # Output the result as JSON.
    import json
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")