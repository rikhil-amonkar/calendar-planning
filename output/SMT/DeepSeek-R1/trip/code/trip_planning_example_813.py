from z3 import *

s = Solver()

# Define cities
Seville, Vilnius, Santorini, London, Stuttgart, Dublin, Frankfurt = 0, 1, 2, 3, 4, 5, 6
cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']

current_city = [Int(f'current_city_{i}') for i in range(17)]

# Ensure each current_city is valid (0-6)
for i in range(17):
    s.add(current_city[i] >= 0, current_city[i] <= 6)

# Flight transition constraints based on direct flights
allowed_flights = [
    (Frankfurt, Dublin), (Dublin, Frankfurt),
    (Frankfurt, London), (London, Frankfurt),
    (London, Dublin), (Dublin, London),
    (Vilnius, Frankfurt), (Frankfurt, Vilnius),
    (Frankfurt, Stuttgart), (Stuttgart, Frankfurt),
    (Dublin, Seville), (Seville, Dublin),
    (London, Santorini), (Santorini, London),
    (Stuttgart, London), (London, Stuttgart),
    (Santorini, Dublin), (Dublin, Santorini)
]

for i in range(1, 17):
    prev = current_city[i-1]
    curr = current_city[i]
    s.add(Or(curr == prev, Or([And(prev == a, curr == b) for (a, b) in allowed_flights])))

# Presence calculation for each city per day
presence = [[Bool(f'presence_{c}_{i}') for i in range(17)] for c in range(7)]

for c in range(7):
    for i in range(17):
        if i == 0:
            s.add(presence[c][i] == (current_city[i] == c))
        else:
            s.add(presence[c][i] == Or(current_city[i] == c, And(current_city[i-1] == c, current_city[i] != c)))

# Total days constraints
s.add(Sum([If(presence[Seville][i], 1, 0) for i in range(17)]) == 5)
s.add(Sum([If(presence[Vilnius][i], 1, 0) for i in range(17)]) == 3)
s.add(Sum([If(presence[Santorini][i], 1, 0) for i in range(17)]) == 2)
s.add(Sum([If(presence[London][i], 1, 0) for i in range(17)]) == 2)
s.add(Sum([If(presence[Stuttgart][i], 1, 0) for i in range(17)]) == 3)
s.add(Sum([If(presence[Dublin][i], 1, 0) for i in range(17)]) == 3)
s.add(Sum([If(presence[Frankfurt][i], 1, 0) for i in range(17)]) == 5)

# Specific event constraints
# London friends between day 9 and 10 (0-based days 8-9)
s.add(presence[London][8])
s.add(presence[London][9])

# Stuttgart relatives between day 7 and 9 (0-based days 6-8)
s.add(presence[Stuttgart][6])
s.add(presence[Stuttgart][7])
s.add(presence[Stuttgart][8])

if s.check() == sat:
    m = s.model()
    plan = [m.evaluate(current_city[i]).as_long() for i in range(17)]
    print("Day\tCity")
    for day in range(17):
        print(f"{day+1}\t{cities[plan[day]]}")
else:
    print("No valid plan found")