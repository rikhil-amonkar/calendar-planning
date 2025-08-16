from z3 import *
import json

# Define the six cities with fixed durations.
# Mapping: 0: Dublin, 1: Madrid, 2: Oslo, 3: London, 4: Vilnius, 5: Berlin
city_names = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
durations = [3, 2, 3, 2, 3, 5]

# There will be 6 itinerary “slots” – one per city.
# When you are in the i‑th slot you stay (duration) days in that city.
# The flight from the previous city to the next happens on the first day of the next slot.
# (That day counts for both cities.)

# Create Z3 integer variables for the permutation (order) and for the start day of each slot.
# The trip lasts 13 unique days.
o = [Int(f"o{i}") for i in range(6)]  # o[i] is the index (0..5) identifying which city is visited at slot i.
s = [Int(f"s{i}") for i in range(6)]  # s[i] is the start day for slot i

solver = Solver()

# Each o[i] must be one of 0..5 and they must be all distinct.
for i in range(6):
    solver.add(o[i] >= 0, o[i] < 6)
solver.add(Distinct(o))

# Define a helper: given a city variable (0..5), return its duration.
def get_duration(city_var):
    return If(city_var == 0, 3,
           If(city_var == 1, 2,
           If(city_var == 2, 3,
           If(city_var == 3, 2,
           If(city_var == 4, 3,
           If(city_var == 5, 5, 0))))))

# The planning uses overlapping flight days.
# For a slot visited with duration d starting at day s, you are there on days s, s+1, …, s+d-1.
# And if you fly to the next city on day s+d-1, that same day counts for both.
# So we require for i>=1:
#    s[i] == s[i-1] + (duration of city in slot i-1) - 1.
solver.add(s[0] == 1)
for i in range(1, 6):
    solver.add(s[i] == s[i-1] + get_duration(o[i-1]) - 1)

# Total trip length: the last city occupies days s[5] ... s[5] + (duration of o[5]) - 1,
# and the final day must be day 13.
solver.add(s[5] + get_duration(o[5]) - 1 == 13)

# Add event constraints.
# 1. In Dublin (city 0) you must spend 3 days and want to meet friends there sometime between day 7 and day 9.
#    That is, if Dublin is visited in slot i with start day s[i], then its interval [s[i], s[i]+2] must
#    include at least one of 7, 8, or 9.
for i in range(6):
    solver.add(Implies(o[i] == 0,
                Or(And(s[i] <= 7, 7 <= s[i] + 2),
                   And(s[i] <= 8, 8 <= s[i] + 2),
                   And(s[i] <= 9, 9 <= s[i] + 2))))
    
# 2. In Madrid (city 1) you want 2 days, and you plan to visit relatives there between day 2 and day 3.
#    Madrid’s interval is [s[i], s[i]+1] so it must include 2 or 3.
for i in range(6):
    solver.add(Implies(o[i] == 1,
                Or(And(s[i] <= 2, 2 <= s[i] + 1),
                   And(s[i] <= 3, 3 <= s[i] + 1))))

# 3. In Berlin (city 5) you stay 5 days, and you have a wedding there between day 3 and day 7.
#    (Since Berlin’s interval is [s[i], s[i]+4], it will include day 7 if s[i] <= 7.)
for i in range(6):
    solver.add(Implies(o[i] == 5, s[i] <= 7))

# (Oslo, London, Vilnius – their durations are fixed by the problem statement.)

# Define allowed direct flight connections.
# A flight from city A to city B is allowed if (A, B) is in the following list:
#   London and Madrid,
#   Oslo and Vilnius,
#   Berlin and Vilnius,
#   Madrid and Oslo,
#   Madrid and Dublin,
#   London and Oslo,
#   Madrid and Berlin,
#   Berlin and Oslo,
#   Dublin and Oslo,
#   London and Dublin,
#   London and Berlin,
#   Berlin and Dublin.
# We assume flights are bidirectional. Using our indices:
#   London (3) – Madrid (1)
#   Oslo (2) – Vilnius (4)
#   Berlin (5) – Vilnius (4)
#   Madrid (1) – Oslo (2)
#   Madrid (1) – Dublin (0)
#   London (3) – Oslo (2)
#   Madrid (1) – Berlin (5)
#   Berlin (5) – Oslo (2)
#   Dublin (0) – Oslo (2)
#   London (3) – Dublin (0)
#   London (3) – Berlin (5)
#   Berlin (5) – Dublin (0)
def allowed(a, b):
    return Or(And(a == 0, b == 1), And(a == 1, b == 0),      # Dublin <-> Madrid
              And(a == 3, b == 1), And(a == 1, b == 3),      # London <-> Madrid
              And(a == 2, b == 4), And(a == 4, b == 2),      # Oslo <-> Vilnius
              And(a == 1, b == 2), And(a == 2, b == 1),      # Madrid <-> Oslo
              And(a == 3, b == 2), And(a == 2, b == 3),      # London <-> Oslo
              And(a == 1, b == 5), And(a == 5, b == 1),      # Madrid <-> Berlin
              And(a == 5, b == 2), And(a == 2, b == 5),      # Berlin <-> Oslo
              And(a == 0, b == 2), And(a == 2, b == 0),      # Dublin <-> Oslo
              And(a == 3, b == 0), And(a == 0, b == 3),      # London <-> Dublin
              And(a == 3, b == 5), And(a == 5, b == 3),      # London <-> Berlin
              And(a == 5, b == 0), And(a == 0, b == 5))      # Berlin <-> Dublin

# For every transition from slot i to slot i+1, the pair of cities must be connected by a direct flight.
for i in range(5):
    solver.add(allowed(o[i], o[i+1]))

# Solve the constraints.
if solver.check() == sat:
    m = solver.model()
    itinerary_slots = []
    # Compute each slot's city and its interval [start, end].
    for i in range(6):
        city_idx = m.evaluate(o[i]).as_long()
        start_day = m.evaluate(s[i]).as_long()
        # Get duration from our fixed list (using our mapping order)
        dur = durations[city_idx]
        itinerary_slots.append((city_idx, start_day, start_day + dur - 1))
        
    # Build the daily itinerary for days 1 to 13.
    # A day might be part of two slots when it is a flight (overlap day).
    day_itinerary = []
    for day in range(1, 14):
        places_today = []
        for (city_idx, start_day, end_day) in itinerary_slots:
            if start_day <= day <= end_day:
                places_today.append(city_names[city_idx])
        day_itinerary.append({"day": day, "places": places_today})
    
    # Final JSON output dictionary.
    result = {"itinerary": day_itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")