from z3 import *

s = Solver()

# Define cities and their indices
Prague, Warsaw, Dublin, Athens, Vilnius, Porto, London, Seville, Lisbon, Dubrovnik = 0, 1, 2, 3, 4, 5, 6, 7, 8, 9
cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']

current_city = [Int(f'current_city_{i}') for i in range(26)]

# Ensure each current_city is valid (0-9)
for i in range(26):
    s.add(current_city[i] >= 0, current_city[i] <= 9)

# Define direct flights (bidirectional)
allowed_flights = [
    (Warsaw, Vilnius), (Vilnius, Warsaw),
    (Prague, Athens), (Athens, Prague),
    (London, Lisbon), (Lisbon, London),
    (Lisbon, Porto), (Porto, Lisbon),
    (Prague, Lisbon), (Lisbon, Prague),
    (London, Dublin), (Dublin, London),
    (Athens, Vilnius), (Vilnius, Athens),
    (Athens, Dublin), (Dublin, Athens),
    (Prague, London), (London, Prague),
    (London, Warsaw), (Warsaw, London),
    (Dublin, Seville), (Seville, Dublin),
    (Seville, Porto), (Porto, Seville),
    (Lisbon, Athens), (Athens, Lisbon),
    (Dublin, Porto), (Porto, Dublin),
    (Athens, Warsaw), (Warsaw, Athens),
    (Lisbon, Warsaw), (Warsaw, Lisbon),
    (Porto, Warsaw), (Warsaw, Porto),
    (Prague, Warsaw), (Warsaw, Prague),
    (Prague, Dublin), (Dublin, Prague),
    (Athens, Dubrovnik), (Dubrovnik, Athens),
    (Lisbon, Dublin), (Dublin, Lisbon),
    (Dubrovnik, Dublin), (Dublin, Dubrovnik),
    (Lisbon, Seville), (Seville, Lisbon),
    (London, Athens), (Athens, London)
]

# Flight transition constraints
for i in range(1, 26):
    prev = current_city[i-1]
    curr = current_city[i]
    s.add(Or(curr == prev, Or([And(prev == a, curr == b) for (a, b) in allowed_flights])))

# Presence calculation for each city per day
presence = [[Bool(f'presence_{c}_{i}') for i in range(26)] for c in range(10)]

for c in range(10):
    for i in range(26):
        if i == 0:
            s.add(presence[c][i] == (current_city[i] == c))
        else:
            s.add(presence[c][i] == Or(current_city[i] == c, And(current_city[i-1] == c, current_city[i] != c)))

# Total days constraints
s.add(Sum([If(presence[Prague][i], 1, 0) for i in range(26)]) == 3)
s.add(Sum([If(presence[Warsaw][i], 1, 0) for i in range(26)]) == 4)
s.add(Sum([If(presence[Dublin][i], 1, 0) for i in range(26)]) == 3)
s.add(Sum([If(presence[Athens][i], 1, 0) for i in range(26)]) == 3)
s.add(Sum([If(presence[Vilnius][i], 1, 0) for i in range(26)]) == 4)
s.add(Sum([If(presence[Porto][i], 1, 0) for i in range(26)]) == 5)
s.add(Sum([If(presence[London][i], 1, 0) for i in range(26)]) == 3)
s.add(Sum([If(presence[Seville][i], 1, 0) for i in range(26)]) == 2)
s.add(Sum([If(presence[Lisbon][i], 1, 0) for i in range(26)]) == 5)
s.add(Sum([If(presence[Dubrovnik][i], 1, 0) for i in range(26)]) == 3)

# Specific event constraints (zero-based days)
# Prague workshop days 0-2 (original 1-3)
for i in [0,1,2]:
    s.add(presence[Prague][i])

# Warsaw friends days 19-22 (original 20-23)
for i in range(19, 23):
    s.add(presence[Warsaw][i])

# Porto conference days 15-19 (original 16-20)
for i in range(15, 20):
    s.add(presence[Porto][i])

# London wedding days 2-4 (original 3-5)
for i in range(2, 5):
    s.add(presence[London][i])

# Lisbon relatives days 4-8 (original 5-9)
for i in range(4, 9):
    s.add(presence[Lisbon][i])

# Enforce no presence outside event days for constrained cities
for i in range(26):
    if i not in [0,1,2]:
        s.add(Not(presence[Prague][i]))
    if i <19 or i >=23:
        s.add(Not(presence[Warsaw][i]))
    if i <15 or i >=20:
        s.add(Not(presence[Porto][i]))
    if i <2 or i >=5:
        s.add(Not(presence[London][i]))
    if i <4 or i >=9:
        s.add(Not(presence[Lisbon][i]))

if s.check() == sat:
    m = s.model()
    plan = [m.evaluate(current_city[i]).as_long() for i in range(26)]
    print("Day\tCity")
    for day in range(26):
        print(f"{day+1}\t{cities[plan[day]]}")
else:
    print("No valid plan found")