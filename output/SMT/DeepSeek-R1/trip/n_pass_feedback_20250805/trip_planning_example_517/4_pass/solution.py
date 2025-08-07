from z3 import *

# Define city mapping
city_map = {
    0: "Dubrovnik",
    1: "Warsaw",
    2: "Stuttgart",
    3: "Bucharest",
    4: "Copenhagen"
}

# Allowed direct flight pairs (bidirectional)
allowed_pairs = [
    (0, 4), (4, 0),  # Dubrovnik - Copenhagen
    (1, 4), (4, 1),  # Warsaw - Copenhagen
    (2, 4), (4, 2),  # Stuttgart - Copenhagen
    (1, 2), (2, 1),  # Warsaw - Stuttgart
    (3, 4), (4, 3),  # Bucharest - Copenhagen
    (3, 1), (1, 3)   # Bucharest - Warsaw
]

# Create Z3 solver
s = Solver()

# Create arrays for start (S) and end (E) cities for each day (19 days)
S = [Int('S_%d' % i) for i in range(19)]
E = [Int('E_%d' % i) for i in range(19)]

# Each S and E must be between 0 and 4
for i in range(19):
    s.add(S[i] >= 0, S[i] <= 4)
    s.add(E[i] >= 0, E[i] <= 4)

# Continuity constraint: start of next day is end of current day
for i in range(18):
    s.add(S[i+1] == E[i])

# Flight constraints: if start and end differ, must be an allowed flight
for i in range(19):
    same_city = S[i] == E[i]
    valid_flight = Or([And(S[i] == a, E[i] == b) for (a, b) in allowed_pairs])
    s.add(Or(same_city, valid_flight))

# Bucharest wedding constraint: must be in Bucharest on at least one day from 1 to 6
wedding_constraint = Or([Or(S[i] == 3, E[i] == 3) for i in range(6)])
s.add(wedding_constraint)

# Stuttgart conference constraints: must be in Stuttgart at the END of days 7 and 13
s.add(E[6] == 2)   # End of day 7 (index 6) must be Stuttgart
s.add(E[12] == 2)  # End of day 13 (index 12) must be Stuttgart

# Count days for each city (each day contributes if city is start or end)
totals = [0] * 5
for a in range(5):
    total = 0
    for i in range(19):
        total += If(Or(S[i] == a, E[i] == a), 1, 0)
    totals[a] = total

# Add constraints for required days per city
s.add(totals[0] == 5)  # Dubrovnik
s.add(totals[1] == 2)  # Warsaw
s.add(totals[2] == 7)  # Stuttgart
s.add(totals[3] == 6)  # Bucharest
s.add(totals[4] == 3)  # Copenhagen

# Solve and output itinerary
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(19):
        city_index = model[E[i]].as_long()
        itinerary.append(city_map[city_index])
    result = {'itinerary': itinerary}
    print(result)
else:
    print("No solution found")