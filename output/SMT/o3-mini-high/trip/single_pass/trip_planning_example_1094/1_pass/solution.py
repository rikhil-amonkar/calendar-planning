from z3 import *
import json

# We label our 8 cities as follows:
# 0: Vienna      (4 days)
# 1: Barcelona   (2 days)
# 2: Edinburgh   (4 days) – must have a friend‐meeting day in [12,15]
# 3: Krakow      (3 days)
# 4: Riga        (4 days)
# 5: Hamburg     (2 days) – its flight day must be day 10 (so its visit is days 10–11 and the conference is on days 10–11)
# 6: Paris       (2 days) – wedding in Paris must occur on day 1 or 2 (i.e. its visit must cover one of these)
# 7: Stockholm   (2 days) – relatives in Stockholm must be visited on day 15 or 16

# Duration table by city index (duration “d” for each city)
dur_by_index = {
    0: 4,  # Vienna
    1: 2,  # Barcelona
    2: 4,  # Edinburgh
    3: 3,  # Krakow
    4: 4,  # Riga
    5: 2,  # Hamburg
    6: 2,  # Paris
    7: 2   # Stockholm
}

# For nicer output
city_names = {
    0: "Vienna",
    1: "Barcelona",
    2: "Edinburgh",
    3: "Krakow",
    4: "Riga",
    5: "Hamburg",
    6: "Paris",
    7: "Stockholm"
}

# Allowed direct flight connections (edges) are given as pairs.
# (For example, "Hamburg and Stockholm" is represented by (5,7).)
# We assume flights are bidirectional so both (a,b) and (b,a) are allowed.
allowed_edges = [
    (5,7),   # Hamburg – Stockholm
    (0,7),   # Vienna – Stockholm
    (6,2),   # Paris – Edinburgh
    (4,1),   # Riga – Barcelona
    (6,4),   # Paris – Riga
    (3,1),   # Krakow – Barcelona
    (2,7),   # Edinburgh – Stockholm
    (6,3),   # Paris – Krakow
    (3,7),   # Krakow – Stockholm
    (4,2),   # Riga – Edinburgh
    (1,7),   # Barcelona – Stockholm
    (6,7),   # Paris – Stockholm
    (3,2),   # Krakow – Edinburgh
    (0,5),   # Vienna – Hamburg
    (6,5),   # Paris – Hamburg
    (4,7),   # Riga – Stockholm
    (5,1),   # Hamburg – Barcelona
    (0,1),   # Vienna – Barcelona
    (3,0),   # Krakow – Vienna
    (4,5),   # Riga – Hamburg
    (1,2),   # Barcelona – Edinburgh
    (6,1),   # Paris – Barcelona
    (5,2),   # Hamburg – Edinburgh
    (6,0),   # Paris – Vienna
    (0,4)    # Vienna – Riga
]

# Create the solver
solver = Solver()

# We choose an ordering of the 8 cities. Let "order" be an array of 8 Int variables,
# each representing one city index. They must all be different.
order = [Int(f"order_{i}") for i in range(8)]
for i in range(8):
    solver.add(order[i] >= 0, order[i] < 8)
solver.add(Distinct(order))

# The trip is planned for 16 distinct days.
# We model the itinerary as 8 “segments” – one per city.
# The rule is: the visit for a city at position i starts on day s_i and lasts for d days.
# Moreover, if you fly from city A to city B on day X,
# then day X counts both as the last day for A and the first day for B.
# (Thus, if s_i is the start day for the i-th city, then its visit covers days s_i, s_i+1, …, s_i+d-1.)
# We always fix s_0 = 1.
start_times = [Int(f"s_{i}") for i in range(8)]
solver.add(start_times[0] == 1)
# For i>=1, s[i] = s[i-1] + (duration of previous city) - 1.
def get_duration(city_var):
    # Given a city (symbolic integer from 0 to 7), return its duration.
    return If(city_var == 0, 4,
           If(city_var == 1, 2,
           If(city_var == 2, 4,
           If(city_var == 3, 3,
           If(city_var == 4, 4,
           If(city_var == 5, 2,
           If(city_var == 6, 2,
           If(city_var == 7, 2, 0))))))))

for i in range(1, 8):
    solver.add(start_times[i] == start_times[i-1] + get_duration(order[i-1]) - 1)

# Now add the special scheduling constraints

# 1. Hamburg (index 5) must be visited so that its start day is 10.
for i in range(8):
    solver.add(Implies(order[i] == 5, start_times[i] == 10))

# 2. Wedding in Paris must occur between day 1 and day 2.
# Since Paris (index 6) is 2 days long, its visit [s, s+1] must overlap {1,2}.
# This is ensured by requiring its start day <= 2.
for i in range(8):
    solver.add(Implies(order[i] == 6, start_times[i] <= 2))

# 3. Friend meeting in Edinburgh (index 2) must fall between day 12 and day 15.
# Edinburgh’s 4‐day visit covers [s, s+3]. For this to intersect [12,15] we require:
#    s <= 15 and s+3 >= 12  <=>  s <= 15 and s >= 9.
for i in range(8):
    solver.add(Implies(order[i] == 2, And(start_times[i] <= 15, start_times[i] >= 9)))

# 4. Relatives in Stockholm (index 7) must be visited between day 15 and day 16.
# Stockholm’s 2‐day visit is [s, s+1]. To cover day 15 or 16, we require s to be 14 or 15.
for i in range(8):
    solver.add(Implies(order[i] == 7, Or(start_times[i] == 14, start_times[i] == 15)))

# 5. Direct flights: For each consecutive pair in the itinerary,
# there must be a direct flight between the cities.
# (Remember that flights are bidirectional.)
for i in range(7):
    # For adjacent positions, one of the allowed flight pairs must hold.
    # We add both (a,b) and (b,a) for each allowed edge.
    flight_options = []
    for (a, b) in allowed_edges:
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    solver.add(Or(flight_options))

# The overall itinerary’s days come out as:
# total distinct days = (sum of durations) - (number of flight overlaps) = 23 - 7 = 16.
# (This is automatically enforced by our start-time definitions.)

# Solve the constraints.
if solver.check() == sat:
    m = solver.model()
    itinerary = []
    for i in range(8):
        city_idx = m.evaluate(order[i]).as_long()
        start_day = m.evaluate(start_times[i]).as_long()
        duration = dur_by_index[city_idx]
        end_day = start_day + duration - 1
        itinerary.append({
            "city": city_names[city_idx],
            "start_day": start_day,
            "end_day": end_day
        })
    # For example, one valid solution is:
    #   Paris:      Days 1–2         (wedding in Paris on day 1–2)
    #   Krakow:     Days 2–4
    #   Vienna:     Days 4–7
    #   Riga:       Days 7–10
    #   Hamburg:    Days 10–11       (conference on days 10–11)
    #   Edinburgh:  Days 11–14       (friend meeting between 12–15)
    #   Stockholm:  Days 14–15       (relatives on day 15)
    #   Barcelona:  Days 15–16
    #
    # Note: Flight days “overlap” the two visits.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")