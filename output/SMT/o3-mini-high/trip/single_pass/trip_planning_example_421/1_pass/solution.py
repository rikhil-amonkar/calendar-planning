from z3 import *
import json

# Define the five cities and assign each an integer index.
# 0: Nice, 1: Krakow, 2: Dublin, 3: Lyon, 4: Frankfurt
cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
# Fixed number of days to spend in each city:
# Nice = 5, Krakow = 6, Dublin = 7, Lyon = 4, Frankfurt = 2.
durations = [5, 6, 7, 4, 2]

# Allowed direct flight connections (bidirectional)
# (a, b) means you can fly directly between a and b.
allowed_edges = [
    (0, 2), (2, 0),   # Nice <-> Dublin
    (2, 4), (4, 2),   # Dublin <-> Frankfurt
    (2, 1), (1, 2),   # Dublin <-> Krakow
    (1, 4), (4, 1),   # Krakow <-> Frankfurt
    (3, 4), (4, 3),   # Lyon   <-> Frankfurt
    (0, 4), (4, 0),   # Nice   <-> Frankfurt
    (3, 2), (2, 3),   # Lyon   <-> Dublin
    (0, 3), (3, 0)    # Nice   <-> Lyon
]

# We will decide the order in which the traveler visits the 5 cities.
# Since the flight day counts toward both cities, if you have an itinerary:
#   City1 for d1 days, then fly on day d1 to City2 (so day d1 counts for both),
# the overall distinct days will be d1 + d2 - 1.
# With 5 cities the total distinct days will be:
#   d1 + d2 + d3 + d4 + d5 - 4.
# Our durations sum 5+6+7+4+2 = 24 so 24 - 4 = 20 days.
#
# We also have two extra time‐window constraints:
#  • You must “visit relatives in Nice” sometime in between Day 1 and Day 5.
#    (i.e. at least one day of your Nice visit must fall on or before day 5.)
#  • You must “meet your friends at Frankfurt” on day 19 or day 20.
#
# Note: Since flying always happens at the very end of a block (and the arrival day
# is the same day as departure’s last day) we “overlap” days, so our block start days
# are defined as follows:
#
#   Let s[0] = 1.
#   For i = 0,1,2,3: s[i+1] = s[i] + duration(p[i]) - 1.
#   The i-th city is visited on every day in [s[i], s[i] + duration(p[i]) - 1].
#
# The itinerary will be represented as a permutation of 5 cities.
# Additional constraints:
#   - Frankfurt (city index 4) must be visited last to meet the "friends" constraint.
#   - If Nice is visited in any block (say block i), the start day of that block (s[i])
#     must be <= 5 so that at least one day in Nice is between day 1 and day 5.
#   - Consecutive cities (in the permutation) must be connected by a direct flight.

# Create 5 integer decision variables for the order (perm of {0,1,2,3,4}).
p = [Int(f"p{i}") for i in range(5)]

s = Solver()

# Each city variable must be between 0 and 4.
for i in range(5):
    s.add(And(p[i] >= 0, p[i] < 5))
# All cities are distinct.
s.add(Distinct(p))
# Frankfurt (index 4) must be visited last.
s.add(p[4] == 4)

# Add direct-flight connectivity constraints:
# For each consecutive pair (p[i], p[i+1]) the flight must be allowed.
for i in range(4):
    a = p[i]
    b = p[i+1]
    allowed_flight = []
    for (a_val, b_val) in allowed_edges:
        allowed_flight.append(And(a == a_val, b == b_val))
    s.add(Or(allowed_flight))

# Helper: returns the duration for a given (symbolic) city value.
def get_duration(city):
    # Use nested Ifs to return the proper duration.
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
              durations[4]))))

# Compute the start day for each block.
# Let S0 = 1 and for i >= 0, S[i+1] = S[i] + get_duration(p[i]) - 1.
s_start = [Int(f"S{i}") for i in range(5)]
s.add(s_start[0] == 1)
for i in range(4):
    s.add(s_start[i+1] == s_start[i] + get_duration(p[i]) - 1)

# Constraint for "visit relatives in Nice between day 1 and day 5":
# If a block corresponds to Nice (city 0), its start day must be <= 5.
for i in range(5):
    s.add(Implies(p[i] == 0, s_start[i] <= 5))

# (The meeting friends constraint at Frankfurt is automatically met if Frankfurt is last.
#  For the fixed durations, the last block will start on day 19:
#    S[4] = (duration(p0) + duration(p1) + duration(p2) + duration(p3)) - 3.
#  And then Frankfurt’s block covers days S[4] to S[4] + 2 - 1 = S[4] + 1.
#  With the durations of the other 4 cities summing to 5+6+7+4 = 22, we have
#    S[4] = 22 - 3 = 19, so Frankfurt is visited on days 19 and 20.)
    
# Try to solve the constraints.
if s.check() == sat:
    m = s.model()
    order = [m[p[i]].as_long() for i in range(5)]
    
    # Compute the start and end day for each city block according to the found order.
    blocks = []  # Each block: (city_name, start_day, end_day)
    current_day = 1
    for idx in order:
        d = durations[idx]
        block_start = current_day
        block_end = block_start + d - 1
        blocks.append((cities[idx], block_start, block_end))
        # The flight means the next block starts on the same day as the current block's end.
        current_day = block_end

    # Build the day-by-day itinerary.
    # On any day, a city block covers that day if day is in [start, end].
    # On flight days the day belongs to both the arriving and departing city.
    itinerary = []
    for day in range(1, 21):
        cities_today = []
        for (name, start_day, end_day) in blocks:
            if day >= start_day and day <= end_day:
                cities_today.append(name)
        # Join multiple cities with a comma for flight days.
        itinerary.append({"day": day, "city": ", ".join(cities_today)})
    
    # Output the JSON dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")