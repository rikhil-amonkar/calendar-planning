from z3 import *
import json

# We have 6 cities with fixed durations:
#   Hamburg: 2 days        (and meet friends there on day 1–2)
#   Dublin: 5 days         (and from day 2 to 6 there is a show)
#   Helsinki: 4 days
#   Reykjavik: 2 days      (and there’s a wedding in Reykjavik between day 9 and 10)
#   London: 5 days
#   Mykonos: 3 days
#
# The total “city‐days” adds up to 2+5+4+2+5+3 = 21. Because when flying between cities on a transfer day that day counts for both
# the city you leave and the city you arrive in, the calendar total becomes:
#   21 – (number of flights)
# and we want a 16–day trip so we must have exactly 5 flights.
#
# The allowed direct flights (bi‐directional) are:
#   Dublin – London 
#   Hamburg – Dublin 
#   Helsinki – Reykjavik 
#   Hamburg – London 
#   Dublin – Helsinki 
#   Reykjavik – London 
#   London – Mykonos 
#   Dublin – Reykjavik 
#   Hamburg – Helsinki 
#   Helsinki – London
#
# We want to assign an ordering (sequence of segments) to the visits.
# Notice that some events force parts of the order:
#   • Hamburg must be at the very start so that you can “meet your friends” on day 1 (and day 2 is also in Hamburg).
#   • Dublin must cover days 2–6 exactly. Since the first segment covers day 1–2, the second segment must start on day 2.
#   • The wedding in Reykjavik between days 9–10 forces the Reykjavik visit to cover day 9 and day 10.
#
# A little reasoning shows that one valid order is:
#
#   Segment 0: Hamburg (2 days)    → covers day 1 and day 2
#   Segment 1: Dublin  (5 days)     → starts on day 2, covers days 2–6 (attend show)
#   Segment 2: Helsinki (4 days)    → starts on day 6, covers days 6–9
#   Segment 3: Reykjavik (2 days)   → must start on day 9 so that it covers days 9–10 (wedding)
#   Segment 4: London (5 days)      → starts on day 10, covers days 10–14
#   Segment 5: Mykonos (3 days)     → starts on day 14, covers days 14–16
#
# Check the flight connections between consecutive segments:
#   Hamburg → Dublin       (allowed: Hamburg–Dublin)
#   Dublin → Helsinki      (allowed: Dublin–Helsinki)
#   Helsinki → Reykjavik   (allowed: Helsinki–Reykjavik)
#   Reykjavik → London     (allowed: Reykjavik–London)
#   London → Mykonos       (allowed: London–Mykonos)
#
# Also note: The flight day is the first day of a segment (except for the very first day),
# so for example day 2 is counted both for Hamburg (last day of segment 0) and Dublin (first day of segment 1).

# Define the fixed order and durations.
order = ["Hamburg", "Dublin", "Helsinki", "Reykjavik", "London", "Mykonos"]
durations = {
    "Hamburg": 2,
    "Dublin": 5,
    "Helsinki": 4,
    "Reykjavik": 2,
    "London": 5,
    "Mykonos": 3
}

# Allowed flights are given as undirected pairs (using frozenset for easy membership tests)
allowed_flights = {
    frozenset(["Dublin", "London"]),
    frozenset(["Hamburg", "Dublin"]),
    frozenset(["Helsinki", "Reykjavik"]),
    frozenset(["Hamburg", "London"]),
    frozenset(["Dublin", "Helsinki"]),
    frozenset(["Reykjavik", "London"]),
    frozenset(["London", "Mykonos"]),
    frozenset(["Dublin", "Reykjavik"]),
    frozenset(["Hamburg", "Helsinki"]),
    frozenset(["Helsinki", "London"])
}

# We'll have one segment per city visit. For each segment, define a start day variable.
# By our model, if a segment i starts at day s[i] and lasts d days, it covers days:
#    s[i], s[i]+1, ..., s[i] + d - 1.
# And when flying from city i to city i+1, the flight occurs on day s[i+1] which is also counted for city i.
num_segments = len(order)
s_days = [Int(f"s_{i}") for i in range(num_segments)]
solver = Solver()

# The first segment (Hamburg) must start on day 1.
solver.add(s_days[0] == 1)

# Each subsequent segment starts on the previous segment's start day plus (duration - 1)
for i in range(1, num_segments):
    solver.add(s_days[i] == s_days[i-1] + durations[order[i-1]] - 1)

# The total trip lasts 16 days. That is, the last segment ends on day 16.
# End day for segment i = s_days[i] + durations[order[i]] - 1.
solver.add(s_days[num_segments - 1] + durations[order[num_segments - 1]] - 1 == 16)

# Special event constraints:
# 1. Dublin show: Dublin must cover days 2–6.
#    Because segment 1 (Dublin) starts on day 2 and lasts 5 days, it covers days 2,3,4,5,6.
solver.add(s_days[1] == 2)

# 2. Wedding in Reykjavik between day 9 and day 10.
#    Since Reykjavik lasts 2 days, it must begin on day 9 (covering days 9 and 10).
#    In our order, Reykjavik is segment 3.
solver.add(s_days[3] == 9)

# 3. (Hamburg friend meeting between day 1 and day 2 is automatically satisfied because segment 0 is Hamburg.)

# Flight constraints: Every consecutive pair of cities must have a direct flight.
for i in range(num_segments - 1):
    city_from = order[i]
    city_to = order[i+1]
    if frozenset([city_from, city_to]) not in allowed_flights:
        # If a direct flight is not allowed, add an unsatisfiable constraint.
        solver.add(False)

# Solve the model.
if solver.check() == sat:
    model = solver.model()
    # Build the itinerary: for each day 1..16, list which city (or cities on a flight day) you are in.
    # (If a flight occurs on day X, then that day is in both the city you left and the city you arrived in.)
    itinerary = {day: [] for day in range(1, 17)}
    
    # For each segment, mark its days.
    for i in range(num_segments):
        start_day = model[s_days[i]].as_long()
        d = durations[order[i]]
        end_day = start_day + d - 1
        for day in range(start_day, end_day + 1):
            itinerary[day].append(order[i])
    
    # Create an ordered list with day mappings.
    itinerary_list = []
    for day in range(1, 17):
        itinerary_list.append({"day": day, "cities": itinerary[day]})
    
    output = {"itinerary": itinerary_list}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")