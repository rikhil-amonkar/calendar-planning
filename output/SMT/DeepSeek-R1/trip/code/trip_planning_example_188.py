from z3 import *

s = Solver()

# Cities: 0 = Brussels, 1 = Barcelona, 2 = Split
current_city = [Int(f'current_city_{i}') for i in range(12)]

# Initial city is Brussels on day 1
s.add(current_city[0] == 0)

# Ensure each current_city is valid (0, 1, or 2)
for i in range(12):
    s.add(Or(current_city[i] == 0, current_city[i] == 1, current_city[i] == 2))

# Valid transitions between cities
for i in range(1, 12):
    prev = current_city[i-1]
    curr = current_city[i]
    s.add(Or(
        And(prev == 0, Or(curr == 0, curr == 1)),  # Brussels to Brussels or Barcelona
        And(prev == 1, Or(curr == 1, curr == 0, curr == 2)),  # Barcelona to Barcelona, Brussels, or Split
        And(prev == 2, Or(curr == 2, curr == 1))  # Split to Split or Barcelona
    )

# Presence in each city for each day
presence_bru = [current_city[i] == 0 for i in range(12)]
presence_bar = [current_city[i] == 1 for i in range(12)]
presence_spl = [current_city[i] == 2 for i in range(12)]

# Add flight days (presence in both cities on transition days)
for i in range(1, 12):
    prev = current_city[i-1]
    curr = current_city[i]
    # If there's a flight, add presence in both cities
    s.add(If(prev != curr,
             And(
                 Or(
                     And(prev == 0, curr == 1, Or(presence_bru[i], presence_bar[i])),
                     And(prev == 1, curr == 0, Or(presence_bru[i], presence_bar[i])),
                     And(prev == 1, curr == 2, Or(presence_bar[i], presence_spl[i])),
                     And(prev == 2, curr == 1, Or(presence_bar[i], presence_spl[i]))
                 )
             ),
             True)
    )

# Total days in each city
total_bru = Sum([If(presence_bru[i], 1, 0) for i in range(12)])
total_bar = Sum([If(presence_bar[i], 1, 0) for i in range(12)])
total_spl = Sum([If(presence_spl[i], 1, 0) for i in range(12)])

s.add(total_bru == 2)
s.add(total_bar == 7)
s.add(total_spl == 5)

# Days 1 and 2 must be in Brussels
s.add(presence_bru[0] == True)
s.add(presence_bru[1] == True)

if s.check() == sat:
    m = s.model()
    cities = ['Brussels', 'Barcelona', 'Split']
    plan = []
    current = 0  # Start in Brussels
    for i in range(12):
        current = m.eval(current_city[i]).as_long()
        plan.append(cities[current])
    # Print the plan
    print("Day\tCity")
    for day in range(12):
        print(f"{day+1}\t{plan[day]}")
else:
    print("No valid plan found")