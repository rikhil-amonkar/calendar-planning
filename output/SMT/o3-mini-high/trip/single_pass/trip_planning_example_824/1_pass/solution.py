from z3 import *
import json

# Define cities and their fixed durations.
# We assign each city an id:
# 0: Berlin (5 days)    - Must be visited on days 1-5 (the show)
# 1: Split (3 days)
# 2: Bucharest (3 days)  - Must be visited (in full) between day 13 and day 15 (relatives)
# 3: Riga (5 days)
# 4: Lisbon (3 days)
# 5: Tallinn (4 days)
# 6: Lyon (5 days)       - Must include at least one day between day 7 and day 11 (wedding)
city_names = {0: "Berlin", 1: "Split", 2: "Bucharest", 3: "Riga", 4: "Lisbon", 5: "Tallinn", 6: "Lyon"}
durations = {0: 5, 1: 3, 2: 3, 3: 5, 4: 3, 5: 4, 6: 5}

# There are 7 blocks (cities) in the itinerary. Each block i has:
#  - a city chosen from 0..6 (each used exactly once)
#  - a start day S[i] (an integer from 1 to 22)
#
# Our interpretation is that if a block i runs from S[i] to E[i] (with E[i] = S[i] + duration - 1)
# and if block i+1 begins on day = E[i] (the flight day), then that day counts for both blocks.
#
# In a contiguous itinerary with 7 blocks, the total trip days equals:
#   (sum of durations) - (# of flights) = 28 - 6 = 22.
#
# We must also obey these special constraints:
# - Berlin must be scheduled as the first block (so its show on days 1-5 is covered).
# - The Bucharest block must exactly cover days 13-15, so its start day must be 13.
# - The Lyon block (wedding) must include at least one day in the interval [7,11],
#   which we enforce by requiring that its start day is no later than 11.
#
# Moreover, between consecutive blocks the traveler takes a direct flight.
# On a flight day, the traveler “counts” as being in both cities.
#
# The allowed direct flight connections (bidirectional except for the Riga->Tallinn flight)
# are:
#   • Lisbon ↔ Bucharest
#   • Berlin ↔ Lisbon
#   • Bucharest ↔ Riga
#   • Berlin ↔ Riga
#   • Berlin ↔ Split
#   • Split ↔ Lyon
#   • Lisbon ↔ Riga
#   • Lyon ↔ Lisbon
#   • Berlin ↔ Tallinn
#   • Lyon ↔ Bucharest
#   • Riga -> Tallinn  (only allowed in the direction from Riga to Tallinn)
#
# We now set up the Z3 model.

# Create a solver
s = Solver()

n = 7  # number of city blocks

# pos[i] will be the id of the city chosen at itinerary position i.
pos = [Int(f"pos_{i}") for i in range(n)]
# S[i] will be the start day of the block at position i.
S_arr = [Int(f"S_{i}") for i in range(n)]

# Each pos[i] must be between 0 and 6 and all must be distinct.
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < 7)
s.add(Distinct(pos))

# The itinerary is contiguous.
# Block 0 starts on day 1.
s.add(S_arr[0] == 1)
# For each block i, let its effective duration be determined by its city.
def city_duration(city):
    # Returns the duration for a given city id as an expression.
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
           If(city == 4, durations[4],
           If(city == 5, durations[5],
           durations[6]))))))

# For blocks 0..n-2, the next block's start day equals the previous block's start day plus
# the previous block's duration minus 1 (since the flight day is double‐counted).
for i in range(n-1):
    s.add(S_arr[i+1] == S_arr[i] + city_duration(pos[i]) - 1)

# The last block must end on day 22.
s.add(S_arr[n-1] + city_duration(pos[n-1]) - 1 == 22)

# Special constraints:
# 1. Berlin must be the first block.
s.add(pos[0] == 0)

# 2. Bucharest block must cover days 13-15.
#    Since Bucharest lasts 3 days, its start day must be 13.
for i in range(n):
    # if pos[i] is Bucharest (2), then start day S_arr[i] must be 13.
    s.add(Implies(pos[i] == 2, S_arr[i] == 13))

# 3. The Lyon block (id 6) must include a wedding between days 7 and 11.
#    For a block lasting 5 days, a sufficient condition is that its start day is at most 11.
for i in range(n):
    s.add(Implies(pos[i] == 6, S_arr[i] <= 11))

# Define allowed flight connections between consecutive blocks.
def flight_allowed(c1, c2):
    # Allowed flights are:
    # Lisbon (4) <> Bucharest (2)
    # Berlin (0) <> Lisbon (4)
    # Bucharest (2) <> Riga (3)
    # Berlin (0) <> Riga (3)
    # Berlin (0) <> Split (1)
    # Split (1) <> Lyon (6)
    # Lisbon (4) <> Riga (3)
    # Lyon (6) <> Lisbon (4)
    # Berlin (0) <> Tallinn (5)
    # Lyon (6) <> Bucharest (2)
    # Riga (3) -> Tallinn (5)  (only allowed if c1==3 and c2==5)
    return Or(And(c1 == 4, c2 == 2), And(c1 == 2, c2 == 4),
              And(c1 == 0, c2 == 4), And(c1 == 4, c2 == 0),
              And(c1 == 2, c2 == 3), And(c1 == 3, c2 == 2),
              And(c1 == 0, c2 == 3), And(c1 == 3, c2 == 0),
              And(c1 == 0, c2 == 1), And(c1 == 1, c2 == 0),
              And(c1 == 1, c2 == 6), And(c1 == 6, c2 == 1),
              And(c1 == 4, c2 == 3), And(c1 == 3, c2 == 4),
              And(c1 == 6, c2 == 4), And(c1 == 4, c2 == 6),
              And(c1 == 0, c2 == 5), And(c1 == 5, c2 == 0),
              And(c1 == 6, c2 == 2), And(c1 == 2, c2 == 6),
              And(c1 == 3, c2 == 5)  # Note: the flight from Riga to Tallinn is only allowed in this order.
             )

# Add flight connection constraints for each consecutive pair.
for i in range(n-1):
    s.add(flight_allowed(pos[i], pos[i+1]))

# Check for satisfiability.
if s.check() == sat:
    m = s.model()
    # Extract the chosen order and start days.
    itinerary_blocks = []
    for i in range(n):
        city = m.evaluate(pos[i]).as_long()
        start = m.evaluate(S_arr[i]).as_long()
        dur = durations[city]
        end = start + dur - 1
        itinerary_blocks.append({
            "city": city_names[city],
            "start": start,
            "end": end,
            "duration": dur
        })
    # Now build a day-by-day itinerary.
    # For each day 1 to 22, determine all blocks that cover that day.
    days = {}
    for day in range(1, 23):
        days[day] = []
    for block in itinerary_blocks:
        for d in range(block["start"], block["end"]+1):
            days[d].append(block["city"])
    # Create the final itinerary list as day-to-cities mappings.
    itinerary = []
    for day in range(1, 23):
        itinerary.append({"day": day, "cities": days[day]})
    
    # Prepare final JSON dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")