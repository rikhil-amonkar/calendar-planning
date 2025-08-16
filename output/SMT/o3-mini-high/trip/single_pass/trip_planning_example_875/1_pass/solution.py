from z3 import *
import json

# Cities and their required durations (in days)
# (Remember: When there is a flight on the last day of a stay, that day counts for both cities.)
cities = ["Stuttgart", "Edinburgh", "Athens", "Split", "Krakow", "Venice", "Mykonos"]
# durations for each city (by our ordering of cities):
# Stuttgart:3, Edinburgh:4, Athens:4, Split:2, Krakow:4, Venice:5, Mykonos:4.
durations = [3, 4, 4, 2, 4, 5, 4]

# Allowed direct flights between cities.
# (We assume the flight relation is symmetric.)
# We use the following index mapping:
# 0: Stuttgart, 1: Edinburgh, 2: Athens, 3: Split, 4: Krakow, 5: Venice, 6: Mykonos
def flight_allowed(x, y):
    return Or(
      # Stuttgart (0)–Venice (5)
      And(x == 0, y == 5),
      And(x == 5, y == 0),
      # Stuttgart (0)–Krakow (4)
      And(x == 0, y == 4),
      And(x == 4, y == 0),
      # Stuttgart (0)–Athens (2)
      And(x == 0, y == 2),
      And(x == 2, y == 0),
      # Stuttgart (0)–Edinburgh (1)
      And(x == 0, y == 1),
      And(x == 1, y == 0),
      # Stuttgart (0)–Split (3)
      And(x == 0, y == 3),
      And(x == 3, y == 0),
      # Edinburgh (1)–Krakow (4)
      And(x == 1, y == 4),
      And(x == 4, y == 1),
      # Edinburgh (1)–Athens (2)
      And(x == 1, y == 2),
      And(x == 2, y == 1),
      # Edinburgh (1)–Venice (5)
      And(x == 1, y == 5),
      And(x == 5, y == 1),
      # Krakow (4)–Split (3)
      And(x == 4, y == 3),
      And(x == 3, y == 4),
      # Split (3)–Athens (2)
      And(x == 3, y == 2),
      And(x == 2, y == 3),
      # Venice (5)–Athens (2)
      And(x == 5, y == 2),
      And(x == 2, y == 5),
      # Athens (2)–Mykonos (6)
      And(x == 2, y == 6),
      And(x == 6, y == 2)
    )

# A helper that returns the duration for a city given a Z3 integer (city index).
def city_duration(c):
    return If(c == 0, 3,
           If(c == 1, 4,
           If(c == 2, 4,
           If(c == 3, 2,
           If(c == 4, 4,
           If(c == 5, 5,
           If(c == 6, 4, 0)))))))

# Create the Z3 solver
s = Solver()

# We create seven variables “order[0] … order[6]” that represent which city is visited in each segment.
order = [Int(f"order_{i}") for i in range(7)]
for i in range(7):
    s.add(order[i] >= 0, order[i] < 7)
s.add(Distinct(order))

# Create seven variables S[0] ... S[6] where S[i] represents the start day of the stay for the city
# in position i of the itinerary. (In our model, each flight day is “shared”: S[i] for i>0 equals the day
# that also is the final day of the previous city.)
S_vars = [Int(f"S_{i}") for i in range(7)]
s.add(S_vars[0] == 1)  # itinerary starts on day 1

# For each segment (except the first) the start day is the previous segment’s finish day.
for i in range(1, 7):
    s.add(S_vars[i] == S_vars[i-1] + city_duration(order[i-1]) - 1)

# The finish day for segment i is S[i] + (duration of that city) - 1.
# Since the total itinerary is 20 days, we force the finish day of the last segment to be 20.
s.add(S_vars[6] + city_duration(order[6]) - 1 == 20)

# Flight constraints: for each consecutive pair of cities in the order, a direct flight must exist.
for i in range(6):
    s.add(flight_allowed(order[i], order[i+1]))

# Event constraints:
# • You plan to stay in Stuttgart (index 0, duration 3) and must attend a workshop there between day 11 and 13.
#   For Stuttgart, the stay [S, S+2] must include at least one day in [11,13]. This is equivalent to:
#       S <= 13 and S+2 >= 11   i.e. S in [9, 13].
for i in range(7):
    s.add(Implies(order[i] == 0, And(S_vars[i] <= 13, S_vars[i] >= 9)))

# • You would like to visit Split (index 3, duration 2) and meet your friends in Split between day 13 and 14.
#   The stay [S, S+1] must overlap with [13,14], i.e. S <= 14 and S+1 >= 13  (so S in [12,14]).
for i in range(7):
    s.add(Implies(order[i] == 3, And(S_vars[i] <= 14, S_vars[i] >= 12)))

# • You want to visit Krakow (index 4, duration 4) and meet a friend in Krakow between day 8 and 11.
#   The stay [S, S+3] must overlap with [8,11], i.e. S <= 11 and S+3 >= 8  (so S in [5,11]).
for i in range(7):
    s.add(Implies(order[i] == 4, And(S_vars[i] <= 11, S_vars[i] >= 5)))

# Solve the model.
if s.check() == sat:
    m = s.model()
    # Compute the segments (city, start_day, finish_day) from the model.
    segments = []
    for i in range(7):
        city_index = m[order[i]].as_long()
        start_day = m[S_vars[i]].as_long()
        dur = durations[city_index]
        finish_day = start_day + dur - 1
        segments.append((cities[city_index], start_day, finish_day))
        
    # For the JSON itinerary, we “unroll” day by day.
    # (Remember that if a flight occurs on some day d, then d is in two segments.)
    itinerary = []
    for day in range(1, 21):
        day_cities = []
        for seg in segments:
            # seg is (city, start, finish)
            if seg[1] <= day <= seg[2]:
                day_cities.append(seg[0])
        # If there is exactly one city that day, output it as a string; if two, output a list.
        if len(day_cities) == 1:
            entry = {"day": day, "city": day_cities[0]}
        else:
            entry = {"day": day, "city": day_cities}
        itinerary.append(entry)
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")