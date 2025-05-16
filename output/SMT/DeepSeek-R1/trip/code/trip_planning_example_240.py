from z3 import *

s = Solver()

# Define cities
PRAGUE, BERLIN, TALLINN, STOCKHOLM = 0, 1, 2, 3
cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']

current_city = [Int(f'current_city_{i}') for i in range(12)]

# Ensure each current_city is valid (0-3)
for i in range(12):
    s.add(current_city[i] >= 0, current_city[i] <= 3)

# Flight transition constraints
for i in range(1, 12):
    prev = current_city[i-1]
    curr = current_city[i]
    s.add(Or(
        prev == curr,
        And(prev == PRAGUE, Or(curr == TALLINN, curr == STOCKHOLM)),
        And(prev == BERLIN, Or(curr == TALLINN, curr == STOCKHOLM)),
        And(prev == TALLINN, Or(curr == PRAGUE, curr == BERLIN, curr == STOCKHOLM)),
        And(prev == STOCKHOLM, Or(curr == PRAGUE, curr == BERLIN, curr == TALLINN))
    ))

# Presence calculation for each city per day
presence = {city: [] for city in [PRAGUE, BERLIN, TALLINN, STOCKHOLM]}
presence[PRAGUE].append(current_city[0] == PRAGUE)
presence[BERLIN].append(current_city[0] == BERLIN)
presence[TALLINN].append(current_city[0] == TALLINN)
presence[STOCKHOLM].append(current_city[0] == STOCKHOLM)

for i in range(1, 12):
    prev = current_city[i-1]
    curr = current_city[i]
    presence[PRAGUE].append(Or(curr == PRAGUE, And(prev == PRAGUE, curr != prev)))
    presence[BERLIN].append(Or(curr == BERLIN, And(prev == BERLIN, curr != prev)))
    presence[TALLINN].append(Or(curr == TALLINN, And(prev == TALLINN, curr != prev)))
    presence[STOCKHOLM].append(Or(curr == STOCKHOLM, And(prev == STOCKHOLM, curr != prev)))

# Total days constraints
s.add(Sum([If(p, 1, 0) for p in presence[PRAGUE]]) == 2)
s.add(Sum([If(p, 1, 0) for p in presence[BERLIN]]) == 3)
s.add(Sum([If(p, 1, 0) for p in presence[TALLINN]]) == 5)
s.add(Sum([If(p, 1, 0) for p in presence[STOCKHOLM]]) == 5)

# Conference in Berlin on days 6 and 8 (1-based -> days 5 and 7 0-based)
s.add(presence[BERLIN][5])
s.add(presence[BERLIN][7])

# Stay in Tallinn between day 8 and 12 (1-based -> days 7-11 0-based)
for i in range(7, 12):
    s.add(presence[TALLINN][i])

if s.check() == sat:
    m = s.model()
    plan = [m.eval(current_city[i]).as_long() for i in range(12)]
    print("Day\tCity")
    for day in range(12):
        print(f"{day+1}\t{cities[plan[day]]}")
else:
    print("No valid plan found")