from z3 import Solver, Int, If, And, Or, Distinct, sat
import json

# --- Data definitions ---
# Cities are indexed as follows:
# 0: Vienna, 1: Milan, 2: Rome, 3: Riga, 4: Lisbon, 5: Vilnius, 6: Oslo
city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]

# Required lengths when “staying” in each city.
# (Remember: When you fly into a new city on the flight day it counts for both the previous and the next city.)
required_days = {0: 4, 1: 2, 2: 3, 3: 2, 4: 3, 5: 4, 6: 3}

# Allowed direct flights.
# Many flights are two‐way; however, note the ones listed with “from” are only available in that direction.
allowed_pairs = [
    (0,1), (1,0),              # Vienna ↔ Milan
    (0,5), (5,0),              # Vienna ↔ Vilnius
    (0,4), (4,0),              # Vienna ↔ Lisbon
    (0,3), (3,0),              # Vienna ↔ Riga
    (0,2), (2,0),              # Vienna ↔ Rome
    (0,6), (6,0),              # Vienna ↔ Oslo
    (1,6), (6,1),              # Milan ↔ Oslo
    (5,1), (1,5),              # Vilnius ↔ Milan
    (2,4), (4,2),              # Rome ↔ Lisbon
    (2,6), (6,2),              # Rome ↔ Oslo
    (3,6), (6,3),              # Riga ↔ Oslo
    (3,1), (1,3),              # Riga ↔ Milan
    (4,6), (6,4),              # Lisbon ↔ Oslo
    (2,3),                    # from Rome -> Riga (one‐way)
    (3,5),                    # from Riga -> Vilnius (one‐way)
    (3,4), (4,3),              # Riga ↔ Lisbon
    (1,4), (4,1),              # Milan ↔ Lisbon
    (5,6), (6,5)               # Vilnius ↔ Oslo
]

def flight_allowed(a, b):
    """Returns a Z3 Boolean that is true if there is a direct flight from city a to city b."""
    return Or([And(a == ap, b == bp) for (ap, bp) in allowed_pairs])

def city_length(seg):
    """Given a Z3 Int 'seg' representing the city index, return an expression for its required days."""
    return If(seg == 0, 4,
           If(seg == 1, 2,
           If(seg == 2, 3,
           If(seg == 3, 2,
           If(seg == 4, 3,
           If(seg == 5, 4,
           If(seg == 6, 3, 0))))))

# --- Model variables ---
# We have 7 segments (one visit per city) that together will cover 15 days.
# Because flight days are “overlap” days, the sum of required days (21) minus 6 overlaps gives 15.
n_seg = 7
seg = [Int(f"seg_{i}") for i in range(n_seg)]  # Which city is visited in segment i
s = [Int(f"s_{i}") for i in range(n_seg)]        # Start day of segment i

# --- Solver and constraints ---
solver = Solver()

# Domain: Each seg[i] is between 0 and 6.
for i in range(n_seg):
    solver.add(seg[i] >= 0, seg[i] < 7)

# The first segment must be Vienna because you have a conference there on day 1 
# (and day 1 must be Vienna) and you must also be there on day 4.
solver.add(seg[0] == 0)

# Each city is visited exactly once.
solver.add(Distinct(seg))

# The itinerary starts on day 1.
solver.add(s[0] == 1)

# The duration of segment i (i.e. the number of days "in" that city) is given by required_days.
# And if you take a flight on the last day of a segment, that day counts for both cities.
# Thus, for i from 0 to 5, the start day of segment i+1 is:
#    s[i+1] = s[i] + (required_days for seg[i]) - 1
for i in range(n_seg - 1):
    solver.add(s[i+1] == s[i] + city_length(seg[i]) - 1)

# The last segment must end on day 15.
solver.add(s[n_seg - 1] + city_length(seg[n_seg - 1]) - 1 == 15)

# Ensure that all start days fall within day 1 to day 15.
for i in range(n_seg):
    solver.add(s[i] >= 1, s[i] <= 15)

# Flight constraints: If you fly from segment i to segment i+1 then a direct flight must exist.
for i in range(n_seg - 1):
    solver.add(flight_allowed(seg[i], seg[i+1]))

# Time-window constraints:
# – In Lisbon, you visit relatives between day 11 and day 13. So whichever segment is Lisbon (city index 4)
#   must have its interval [s[i], s[i] + length - 1] intersect [11, 13].
# – In Oslo, you meet your friend between day 13 and day 15. So whichever segment is Oslo (city index 6)
#   must have its interval intersect [13, 15].
for i in range(n_seg):
    dur = city_length(seg[i])
    lisbon_window = And(s[i] <= 13, s[i] + dur - 1 >= 11)
    oslo_window = And(s[i] <= 15, s[i] + dur - 1 >= 13)
    solver.add(If(seg[i] == 4, lisbon_window, True))
    solver.add(If(seg[i] == 6, oslo_window, True))

# --- Solve and extract a solution ---
if solver.check() == sat:
    m = solver.model()
    itinerary_segments = []
    segments_intervals = []  # list of tuples (start_day, end_day, city_name)
    for i in range(n_seg):
        city_idx = m[seg[i]].as_long()
        city = city_names[city_idx]
        # Get the required days (as an integer) for this city
        if city_idx in required_days:
            dur = required_days[city_idx]
        else:
            dur = 0
        start_day = m[s[i]].as_long()
        end_day = start_day + dur - 1
        # Build a segment mapping (note the flight day is the overlap between segments).
        itinerary_segments.append({"city": city, "days": f"{start_day}-{end_day}"})
        segments_intervals.append((start_day, end_day, city))
    
    # Also, build a day-by-day mapping.
    # On a flight day the day is counted for both cities.
    daily = []
    for day in range(1, 16):
        cities_today = []
        for (start_day, end_day, city) in segments_intervals:
            if start_day <= day <= end_day:
                cities_today.append(city)
        daily.append({"day": day, "cities": cities_today})
    
    result = {"itinerary": itinerary_segments, "daily": daily}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")