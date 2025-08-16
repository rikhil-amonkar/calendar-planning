from z3 import *
import json

# We have 7 cities.
# City indices and data:
# 0: Riga (2 days)
# 1: Frankfurt (3 days)
# 2: Amsterdam (2 days)  -- friend meeting must occur here on day 2 or 3
# 3: Vilnius (5 days)     -- workshop must occur here between day 7 and 11 (i.e. some day of the 5‐day block is in 7..11)
# 4: London (2 days)
# 5: Stockholm (3 days)  -- wedding must occur here between day 13 and 15 (i.e. some day of the block is in 13..15)
# 6: Bucharest (4 days)
cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
durations_list = [2, 3, 2, 5, 2, 3, 4]  # corresponding durations

# Allowed direct flight pairs (bidirectional).
# When flying between consecutive cities in the itinerary, the pair must be one of these.
allowed_pairs = [
    (4, 2), (2, 4),      # London <--> Amsterdam
    (3, 1), (1, 3),      # Vilnius <--> Frankfurt
    (0, 3), (3, 0),      # Riga <--> Vilnius   (note: the original said "from Riga to Vilnius", here we treat as bidirectional)
    (0, 5), (5, 0),      # Riga <--> Stockholm
    (4, 6), (6, 4),      # London <--> Bucharest
    (2, 5), (5, 2),      # Amsterdam <--> Stockholm
    (2, 1), (1, 2),      # Amsterdam <--> Frankfurt
    (1, 5), (5, 1),      # Frankfurt <--> Stockholm
    (6, 0), (0, 6),      # Bucharest <--> Riga
    (2, 0), (0, 2),      # Amsterdam <--> Riga
    (2, 6), (6, 2),      # Amsterdam <--> Bucharest
    (0, 1), (1, 0),      # Riga <--> Frankfurt
    (6, 1), (1, 6),      # Bucharest <--> Frankfurt
    (4, 1), (1, 4),      # London <--> Frankfurt
    (4, 5), (5, 4),      # London <--> Stockholm
    (2, 3), (3, 2)       # Amsterdam <--> Vilnius
]

# Create a Z3 solver instance.
solver = Solver()

# We will decide the order by creating an array "pos" of 7 integer variables.
# pos[i] will be the city index visited in the i-th segment.
pos = [Int(f"pos_{i}") for i in range(7)]
for p in pos:
    solver.add(And(p >= 0, p < 7))
solver.add(Distinct(pos))

# Create an array s[0..6] for the start day of each city segment.
# By our modeling, if you fly from city A to city B on day X then X counts for both cities.
# Thus if a city has required days d, its interval is [s, s+d-1].
s = [Int(f"s_{i}") for i in range(7)]
solver.add(s[0] == 1)  # first city starts on day 1

# A helper function to pick the duration for a city variable.
def get_duration(city_var):
    return If(city_var == 0, durations_list[0],
           If(city_var == 1, durations_list[1],
           If(city_var == 2, durations_list[2],
           If(city_var == 3, durations_list[3],
           If(city_var == 4, durations_list[4],
           If(city_var == 5, durations_list[5],
              durations_list[6]))))))

# Recurrence: if city at pos[i] has duration d, then the next city starts on s[i] + (d - 1)
for i in range(6):
    solver.add(s[i+1] == s[i] + (get_duration(pos[i]) - 1))

# The trip must finish exactly on day 15.
# The last city’s interval is [s_6, s_6 + duration - 1] so:
solver.add(s[6] + (get_duration(pos[6]) - 1) == 15)

# Flight connectivity constraints: For every consecutive pair in the itinerary, the pair must be allowed.
for i in range(6):
    u = pos[i]
    v = pos[i+1]
    # Build the disjunction for allowed pairs.
    flight_ok = Or([And(u == a, v == b) for (a, b) in allowed_pairs])
    solver.add(flight_ok)

# Special scheduling constraints:
# 1. Amsterdam friend meeting between day 2 and day 3.
#    Amsterdam (city id 2) is visited for 2 days: its interval is [s, s+1].
#    We require that either day 2 or day 3 is in that interval.
for i in range(7):
    # When the city at position i is Amsterdam, enforce:
    solver.add(Implies(pos[i] == 2, Or(s[i] == 1, s[i] == 2, s[i] == 3)))
    # Explanation:
    # If s[i]==1, interval is [1,2] with friend meeting on day2.
    # If s[i]==2, interval is [2,3] contains day2 and day3.
    # If s[i]==3, interval is [3,4] contains day3.

# 2. Vilnius workshop between day 7 and 11.
#    Vilnius (city id 3) is visited for 5 days: interval [s, s+4].
#    The block must intersect [7,11] <=> s <= 11 and s+4 >= 7, i.e. s in [3,11].
for i in range(7):
    solver.add(Implies(pos[i] == 3, And(s[i] >= 3, s[i] <= 11)))

# 3. Stockholm wedding between day 13 and 15.
#    Stockholm (city id 5) is visited for 3 days: interval [s, s+2].
#    The block must intersect [13,15] <=> s <= 15 and s+2 >= 13, i.e. s >= 11.
for i in range(7):
    solver.add(Implies(pos[i] == 5, And(s[i] <= 15, s[i] + 2 >= 13)))

# Check whether a solution exists.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Compute the itinerary segments.
    for i in range(7):
        city_index = model.evaluate(pos[i]).as_long()
        city_name = cities[city_index]
        start_day = model.evaluate(s[i]).as_long()
        # Get duration for this city
        # (We can get it directly from durations_list using the city_index.)
        d = durations_list[city_index]
        end_day = start_day + d - 1
        itinerary.append({"city": city_name, "start_day": start_day, "end_day": end_day})
    
    # For clarity, sort the itinerary segments by start_day (they are already in order).
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")