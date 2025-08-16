from z3 import *

# Each city and its required number of “stay‐days” (including a flight day that overlaps two cities)
# City codes and durations:
#   0: Porto (5 days)
#   1: Prague (4 days)
#   2: Reykjavik (4 days)
#   3: Santorini (2 days)
#   4: Amsterdam (2 days)
#   5: Munich (4 days)
#
# The travel plan is modeled as a sequence of 6 segments. When you “fly” from one segment to the next,
# the day of the flight counts for both the departing and arriving city.
#
# We already have two “global” conditions on the special cities:
#  • You must be in Reykjavik (2) at some point during days 4–7 (wedding).
#  • You must be in Amsterdam (4) on days 14–15 (conference).
#  • You must be in Munich (5) such that a day between 7 and 10 falls in that stay (friend meeting).
#
# In addition, the allowed direct flights (bidirectional) are:
#   Porto – Amsterdam
#   Munich – Amsterdam
#   Reykjavik – Amsterdam
#   Munich – Porto
#   Prague – Reykjavik
#   Reykjavik – Munich
#   Amsterdam – Santorini
#   Prague – Amsterdam
#   Prague – Munich
#
# Because the “stay‐durations” add to 21 but the 5 flight days are double‐counted, the itinerary
# runs for 16 calendar days. We “overlap” each segment’s last day (flight day) with the next’s first.
#
# Our plan is to have 6 segments, with:
#   Segment i: city p[i], stay from s[i] to e[i], where e[i] = s[i] + duration(p[i]) - 1.
#   We force s[0] = 1 and for i > 0, s[i] = e[i-1].
#   And e[5] must equal 16.
#
# A further arithmetic observation forces Amsterdam to come at segment 4.
# (Because the first four segments must come from the set {Porto, Prague, Reykjavik, Munich} and their
# durations must sum to 17 so that s[4] becomes 14 – exactly the only way to cover the 14–15 Amsterdam conference.)
#
# We also then deduce that the remaining city (Santorini) must be at segment 5.
#
# Finally, for the flight legs among segments 0–3 (all in {Porto, Prague, Reykjavik, Munich}), we only allow
# transitions if the flight is “direct” by the given list. In our model we allow these transitions:
#   • Prague (1) ↔ Reykjavik (2)
#   • Munich (5) ↔ Reykjavik (2)
#   • Prague (1) ↔ Munich (5)
#   • Porto (0) ↔ Munich (5)
#
# The special-event “overlap” conditions are enforced on whichever segment uses the special city.
#
# -------------------------------
# Build the Z3 model:

# Define a helper function to return the required duration based on the city code.
def duration(city):
    return If(city == 0, 5,       # Porto
           If(city == 1, 4,       # Prague
           If(city == 2, 4,       # Reykjavik
           If(city == 3, 2,       # Santorini
           If(city == 4, 2,       # Amsterdam
           If(city == 5, 4, 0))))))

# For flight legs among segments 0..3 (all cities here will be in {0,1,2,5}),
# we define allowed transitions (bidirectional):
#   • Prague (1) and Reykjavik (2)
#   • Reykjavik (2) and Munich (5)
#   • Prague (1) and Munich (5)
#   • Porto (0) and Munich (5)
def allowed_flight(a, b):
    return Or(And(a == 1, b == 2),
              And(a == 2, b == 1),
              And(a == 2, b == 5),
              And(a == 5, b == 2),
              And(a == 1, b == 5),
              And(a == 5, b == 1),
              And(a == 0, b == 5),
              And(a == 5, b == 0))

# Map the numeric codes to city names.
city_names = {0: "Porto", 1: "Prague", 2: "Reykjavik",
              3: "Santorini", 4: "Amsterdam", 5: "Munich"}

# Create the solver.
solver = Solver()

# There are 6 segments. For each segment i:
#   p[i] is an Int representing the visited city.
#   s[i] is the calendar start day of that segment.
p = [Int(f"p{i}") for i in range(6)]
s = [Int(f"s{i}") for i in range(6)]
# Let e[i] be the computed end day: s[i] + duration(p[i]) - 1.
e = [s[i] + duration(p[i]) - 1 for i in range(6)]

# Domain for cities: each p[i] must be in {0,1,2,3,4,5} and all cities are visited exactly once.
for i in range(6):
    solver.add(p[i] >= 0, p[i] <= 5)
solver.add(Distinct(p))

# Based on our deduction:
#   Amsterdam (4) must be segment 4 (to have its two‐day conference fall on days 14–15)
#   Santorini (3) then becomes segment 5.
solver.add(p[4] == 4)  # Amsterdam
solver.add(p[5] == 3)  # Santorini

# The itinerary starts on day 1.
solver.add(s[0] == 1)
# When flying from segment i to i+1 the last day of segment i is also the first day of segment i+1.
for i in range(1, 6):
    solver.add(s[i] == e[i-1])
# The final segment must end on day 16.
solver.add(e[5] == 16)

# For segments 0..3, the visited cities must be exactly {Porto, Prague, Reykjavik, Munich}.
# Their durations are: Porto=5; Prague, Reykjavik, Munich = 4.
# To get the correct overlap (s[4] == 14), the sum of durations for segments 0–3 must be 17:
#   s[4] = 1 + (duration(p0)+...+duration(p3)) - 3.
solver.add(s[4] == 14)
sum_d = duration(p[0]) + duration(p[1]) + duration(p[2]) + duration(p[3])
solver.add(sum_d == 17)
# In practice, since the only way to get 17 from four numbers where one is 5 and the other three are 4,
# exactly one of the segments among 0–3 must be Porto (0).
solver.add(If(p[0] == 0, 1, 0) +
           If(p[1] == 0, 1, 0) +
           If(p[2] == 0, 1, 0) +
           If(p[3] == 0, 1, 0) == 1)

# Add allowed flight transition constraints for the legs among segments 0→1, 1→2, and 2→3.
for i in range(3):
    solver.add(allowed_flight(p[i], p[i+1]))
# (The remaining legs – from segment 3 to 4 and 4 to 5 – are automatically allowed based on the given edges:
#   Porto/Prague/Reykjavik/​Munich → Amsterdam and Amsterdam → Santorini.)

# Event constraints:
# Wedding in Reykjavik: If a segment is in Reykjavik (2), its stay [s, e] must include at least one day between 4 and 7.
# That is, we require s <= 7 and e >= 4.
for i in range(6):
    solver.add(Implies(p[i] == 2, And(s[i] <= 7, e[i] >= 4)))
    
# Amsterdam conference: If a segment is Amsterdam (4), its two‐day block must cover days 14 and 15.
# With duration 2 that forces s == 14.
for i in range(6):
    solver.add(Implies(p[i] == 4, s[i] == 14))
    
# Meeting friend in Munich: If a segment is Munich (5), then its 4‐day block [s, s+3] must include a day between 7 and 10.
# That is, we require s <= 10 and s+3 >= 7.
for i in range(6):
    solver.add(Implies(p[i] == 5, And(s[i] <= 10, s[i] + 3 >= 7)))
    
# Domain for the start days – they must fall between day 1 and day 16.
for i in range(6):
    solver.add(s[i] >= 1, s[i] <= 16)

# -------------------------------
# Solve the model and then output the itinerary as a list
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(6):
        start_day = model.evaluate(s[i]).as_long()
        end_day = model.evaluate(e[i]).as_long()
        city_index = model.evaluate(p[i]).as_long()
        city = city_names[city_index]
        itinerary.append({"start_day": start_day, "end_day": end_day, "city": city})
    
    import json
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")