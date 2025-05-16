from z3 import *

s = Solver()

# Define cities
Hamburg, Zurich, Helsinki, Bucharest, Split = 0, 1, 2, 3, 4
cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']

current_city = [Int(f'current_city_{i}') for i in range(12)]

# Ensure each current_city is valid (0-4)
for i in range(12):
    s.add(current_city[i] >= 0, current_city[i] <= 4)

# Flight transition constraints based on direct flights
allowed_flights = [
    (Zurich, Helsinki), (Helsinki, Zurich),
    (Hamburg, Bucharest), (Bucharest, Hamburg),
    (Helsinki, Hamburg), (Hamburg, Helsinki),
    (Zurich, Hamburg), (Hamburg, Zurich),
    (Zurich, Bucharest), (Bucharest, Zurich),
    (Zurich, Split), (Split, Zurich),
    (Helsinki, Split), (Split, Helsinki),
    (Split, Hamburg), (Hamburg, Split)
]

for i in range(1, 12):
    prev = current_city[i-1]
    curr = current_city[i]
    s.add(Or(curr == prev, Or([And(prev == a, curr == b) for (a, b) in allowed_flights])))

# Presence calculation for each city per day
presence = [[Bool(f'presence_{c}_{i}') for i in range(12)] for c in range(5)]

for c in range(5):
    for i in range(12):
        if i == 0:
            s.add(presence[c][i] == (current_city[i] == c))
        else:
            s.add(presence[c][i] == Or(current_city[i] == c, And(current_city[i-1] == c, current_city[i] != c)))

# Total days constraints
s.add(Sum([If(presence[Hamburg][i], 1, 0) for i in range(12)]) == 2)
s.add(Sum([If(presence[Zurich][i], 1, 0) for i in range(12)]) == 3)
s.add(Sum([If(presence[Helsinki][i], 1, 0) for i in range(12)]) == 2)
s.add(Sum([If(presence[Bucharest][i], 1, 0) for i in range(12)]) == 2)
s.add(Sum([If(presence[Split][i], 1, 0) for i in range(12)]) == 7)

# Specific event constraints
# Zurich wedding days 1-3 (0-based 0-2)
for i in [0, 1, 2]:
    s.add(presence[Zurich][i])

# Split conference days 4-10 (0-based 3-9)
for i in range(3, 10):
    s.add(presence[Split][i])

# Split's presence is only allowed during conference days (3-9)
for i in list(range(0, 3)) + list(range(10, 12)):
    s.add(Not(presence[Split][i]))

if s.check() == sat:
    m = s.model()
    plan = [m.evaluate(current_city[i]).as_long() for i in range(12)]
    print("Day\tCity")
    for day in range(12):
        print(f"{day+1}\t{cities[plan[day]]}")
else:
    print("No valid plan found")