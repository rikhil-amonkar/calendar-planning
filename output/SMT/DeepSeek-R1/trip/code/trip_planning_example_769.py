from z3 import *

s = Solver()

# Define cities
Porto, Prague, Reykjavik, Santorini, Amsterdam, Munich = 0, 1, 2, 3, 4, 5
cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']

current_city = [Int(f'current_city_{i}') for i in range(16)]

# Ensure each current_city is valid (0-5)
for i in range(16):
    s.add(current_city[i] >= 0, current_city[i] <= 5)

# Flight transition constraints based on direct flights
allowed_flights = [
    (Porto, Amsterdam), (Amsterdam, Porto),
    (Munich, Amsterdam), (Amsterdam, Munich),
    (Reykjavik, Amsterdam), (Amsterdam, Reykjavik),
    (Munich, Porto), (Porto, Munich),
    (Prague, Reykjavik), (Reykjavik, Prague),
    (Reykjavik, Munich), (Munich, Reykjavik),
    (Amsterdam, Santorini), (Santorini, Amsterdam),
    (Prague, Amsterdam), (Amsterdam, Prague),
    (Prague, Munich), (Munich, Prague)
]

for i in range(1, 16):
    prev = current_city[i-1]
    curr = current_city[i]
    s.add(Or(curr == prev, Or([And(prev == a, curr == b) for (a, b) in allowed_flights])))

# Presence calculation for each city per day
presence = [[Bool(f'presence_{c}_{i}') for i in range(16)] for c in range(6)]

for c in range(6):
    # Day 0
    s.add(presence[c][0] == (current_city[0] == c))
    # Days 1-15
    for i in range(1, 16):
        s.add(presence[c][i] == Or(current_city[i] == c, And(current_city[i-1] == c, current_city[i] != c))

# Total days constraints
s.add(Sum([If(presence[Porto][i], 1, 0) for i in range(16)]) == 5)
s.add(Sum([If(presence[Prague][i], 1, 0) for i in range(16)]) == 4)
s.add(Sum([If(presence[Reykjavik][i], 1, 0) for i in range(16)]) == 4)
s.add(Sum([If(presence[Santorini][i], 1, 0) for i in range(16)]) == 2)
s.add(Sum([If(presence[Amsterdam][i], 1, 0) for i in range(16)]) == 2)
s.add(Sum([If(presence[Munich][i], 1, 0) for i in range(16)]) == 4)

# Specific event constraints
# Reykjavik wedding (days 4-7 1-based → 3-6 0-based)
for i in [3, 4, 5, 6]:
    s.add(presence[Reykjavik][i])

# Amsterdam conference (days 14-15 1-based → 13-14 0-based)
s.add(presence[Amsterdam][13])
s.add(presence[Amsterdam][14])

# Munich friend meeting (days 7-10 1-based → 6-9 0-based)
for i in [6, 7, 8, 9]:
    s.add(presence[Munich][i])

if s.check() == sat:
    m = s.model()
    plan = [m.evaluate(current_city[i]).as_long() for i in range(16)]
    print("Day\tCity")
    for day in range(16):
        print(f"{day+1}\t{cities[plan[day]]}")
else:
    print("No valid plan found")