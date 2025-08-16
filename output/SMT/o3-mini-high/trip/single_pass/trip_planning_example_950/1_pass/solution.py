from z3 import *
import json

# We assign indices to cities:
# 0: Rome, 1: Mykonos, 2: Riga, 3: Munich, 4: Bucharest, 5: Nice, 6: Krakow
city_names = {0: "Rome", 1: "Mykonos", 2: "Riga", 3: "Munich", 4: "Bucharest", 5: "Nice", 6: "Krakow"}

# fixed durations in each city:
# Rome:4, Mykonos:3, Riga:3, Munich:4, Bucharest:4, Nice:3, Krakow:2
def duration(city):
    return If(city == 0, 4,
           If(city == 1, 3,
           If(city == 2, 3,
           If(city == 3, 4,
           If(city == 4, 4,
           If(city == 5, 3,
           If(city == 6, 2, 0)))))))

# Allowed flight edges.
# When flying from city A (slot i) to city B (slot i+1),
# the flight day is the last day of A and simultaneously the first day of B.
#
# Some pairs are bidirectional (e.g. "Nice and Riga") while
# others are available only in one direction (e.g. "from Rome to Riga" or "from Riga to Munich").
def allowed(a, b):
    return Or(
        # Nice and Riga (bidirectional)
        And(a == 5, b == 2), And(a == 2, b == 5),
        # Bucharest and Munich
        And(a == 4, b == 3), And(a == 3, b == 4),
        # Mykonos and Munich
        And(a == 1, b == 3), And(a == 3, b == 1),
        # Riga and Bucharest
        And(a == 2, b == 4), And(a == 4, b == 2),
        # Rome and Nice
        And(a == 0, b == 5), And(a == 5, b == 0),
        # Rome and Munich
        And(a == 0, b == 3), And(a == 3, b == 0),
        # Mykonos and Nice
        And(a == 1, b == 5), And(a == 5, b == 1),
        # Rome and Mykonos
        And(a == 0, b == 1), And(a == 1, b == 0),
        # Munich and Krakow
        And(a == 3, b == 6), And(a == 6, b == 3),
        # Rome and Bucharest
        And(a == 0, b == 4), And(a == 4, b == 0),
        # Nice and Munich
        And(a == 5, b == 3), And(a == 3, b == 5),
        # from Riga to Munich (directional: only allowed if from Riga (2) to Munich (3))
        And(a == 2, b == 3),
        # from Rome to Riga (directional: only allowed if from Rome (0) to Riga (2))
        And(a == 0, b == 2)
    )

# There are 7 cities (slots)
n_slots = 7

# Create Z3 integer arrays for the city order (P) and the start days (S) 
P = [Int(f"P_{i}") for i in range(n_slots)]
S = [Int(f"S_{i}") for i in range(n_slots)]

solver = Solver()

# Constraint: each slot gets a city (0...6) and they are all different.
for i in range(n_slots):
    solver.add(And(P[i] >= 0, P[i] <= 6))
solver.add(Distinct(P))

# Force Rome to be first and Krakow to be last.
solver.add(P[0] == 0)  # Rome must be visited first so that day 1 and day 4 (conference) occur in Rome.
solver.add(P[n_slots - 1] == 6)  # Krakow is last (to cover the annual show on days16-17).

# The start day for the first city is day 1.
solver.add(S[0] == 1)

# For i = 0,..., n_slots-2: the next city’s start day equals the previous start + (duration of previous city - 1)
for i in range(n_slots - 1):
    solver.add(S[i+1] == S[i] + (duration(P[i]) - 1))

# Total trip length: The last city’s interval is [S[n_slots-1], S[n_slots-1] + duration(P[n_slots-1]) - 1] = [S[6], S[6]+(2-1)]
# So we require S[6] + 1 == 17  i.e. S[6] == 16.
solver.add(S[n_slots - 1] + (duration(P[n_slots - 1]) - 1) == 17)

# Add flight constraints: For each adjacent pair of slots, (P[i], P[i+1]) must be allowed.
for i in range(n_slots - 1):
    solver.add(allowed(P[i], P[i+1]))

# Add the wedding constraint: When Mykonos (city 1) is visited, we must have at least one day between day 4 and 6.
# That is, if slot i is Mykonos then its interval [S_i, S_i + 3 - 1] must intersect [4,6]:
# i.e. S_i <= 6 AND S_i + 2 >= 4.
for i in range(n_slots):
    solver.add(Implies(P[i] == 1, And(S[i] <= 6, S[i] + 2 >= 4)))

# (The conference constraint is satisfied by having Rome in slot 0 which covers days 1-4.)
# (The annual show in Krakow is automatically satisfied by having Krakow last, with S[6]=16 and duration 2 -> [16,17].)

# Solve the model.
if solver.check() == sat:
    model = solver.model()
    # For each slot, compute the city and its start day.
    itinerary_slots = []
    for i in range(n_slots):
        city_idx = model.evaluate(P[i]).as_long()
        start_day = model.evaluate(S[i]).as_long()
        # duration: note we can use the mapping (we know each city’s duration)
        if city_idx == 0:
            dur = 4
        elif city_idx == 1:
            dur = 3
        elif city_idx == 2:
            dur = 3
        elif city_idx == 3:
            dur = 4
        elif city_idx == 4:
            dur = 4
        elif city_idx == 5:
            dur = 3
        elif city_idx == 6:
            dur = 2
        itinerary_slots.append( { "city": city_names[city_idx],
                                  "start": start_day,
                                  "end": start_day + dur - 1,
                                  "duration": dur } )
        
    # For clarity, sort the slots by start day (they are already in order by construction)
    itinerary_slots.sort(key=lambda x: x["start"])
    
    # Build a day-by-day itinerary.
    # For each calendar day from 1 to 17, list each city in which the traveler is present.
    day_plan = {}
    for d in range(1, 18):
        present = []
        for slot in itinerary_slots:
            if d >= slot["start"] and d <= slot["end"]:
                present.append(slot["city"])
        # On flight days there will be 2 cities.
        day_plan[d] = present

    # Build the JSON dictionary with a list of day mappings.
    itinerary = []
    for d in range(1, 18):
        # if more than one city is present, join them with " / " to indicate overlap.
        itinerary.append({ "day": d, "city": " / ".join(day_plan[d]) })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")