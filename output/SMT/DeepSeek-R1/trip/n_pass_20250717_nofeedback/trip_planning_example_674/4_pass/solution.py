from z3 import *

city_names = ['Helsinki', 'Madrid', 'Budapest', 'Reykjavik', 'Warsaw', 'Split']
n_days = 14

s = Solver()

base_city = [Int(f'base_{i}') for i in range(n_days)]
travel = [Bool(f'travel_{i}') for i in range(n_days)]

s.add(base_city[0] == 0)

for i in range(n_days - 1):
    s.add(base_city[i+1] == If(travel[i], base_city[i] + 1, base_city[i]))

for i in range(n_days):
    s.add(base_city[i] >= 0)
    s.add(base_city[i] <= 5)
    s.add(Implies(base_city[i] == 5, Not(travel[i])))

s.add(If(travel[13], base_city[13] + 1, base_city[13]) == 5)

counts = []
for k in range(6):
    non_travel = [If(And(base_city[i] == k, Not(travel[i])), 1, 0) for i in range(n_days)]
    depart = [If(And(base_city[i] == k, travel[i]), 1, 0) for i in range(n_days)]
    if k == 0:
        arrive = []
    else:
        arrive = [If(And(base_city[i] == k-1, travel[i]), 1, 0) for i in range(n_days)]
    total = non_travel + depart + arrive
    counts.append(Sum(total))

for k in range(5):
    s.add(counts[k] >= 3)
s.add(counts[5] >= 1)

if s.check() == sat:
    m = s.model()
    base_vals = [m.evaluate(base_city[i]).as_long() for i in range(n_days)]
    travel_vals = [m.evaluate(travel[i]) for i in range(n_days)]
    itinerary = []
    for i in range(n_days):
        if travel_vals[i]:
            from_city = base_vals[i]
            to_city = base_vals[i] + 1
            itinerary.append([city_names[from_city], city_names[to_city]])
        else:
            itinerary.append([city_names[base_vals[i]]])
    print(itinerary)
else:
    print("No solution found")