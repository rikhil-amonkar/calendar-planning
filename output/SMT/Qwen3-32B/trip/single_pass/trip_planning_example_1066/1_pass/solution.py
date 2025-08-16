from z3 import *

# Define the cities using EnumSort
cities, (Brussels, Bucharest, Stuttgart, Mykonos, Madrid, Helsinki, Split, London) = EnumSort('City', ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London'])

# Create variables for each day (0 to 20, representing days 1 to 21)
days = [Const(f'day_{i}', cities) for i in range(21)]

# Define allowed direct flight pairs (both directions included)
allowed_pairs = [
    (Helsinki, London), (London, Helsinki),
    (Split, Madrid), (Madrid, Split),
    (Helsinki, Madrid), (Madrid, Helsinki),
    (London, Madrid), (Madrid, London),
    (Brussels, London), (London, Brussels),
    (Bucharest, London), (London, Bucharest),
    (Brussels, Bucharest), (Bucharest, Brussels),
    (Bucharest, Madrid), (Madrid, Bucharest),
    (Split, Helsinki), (Helsinki, Split),
    (Mykonos, Madrid), (Madrid, Mykonos),
    (Stuttgart, London), (London, Stuttgart),
    (Helsinki, Brussels), (Brussels, Helsinki),
    (Brussels, Madrid), (Madrid, Brussels),
    (Split, London), (London, Split),
    (Stuttgart, Split), (Split, Stuttgart),
    (London, Mykonos), (Mykonos, London),
]

# Initialize the solver
s = Solver()

# Add constraints for consecutive days to be connected by direct flights
for i in range(20):
    c1 = days[i]
    c2 = days[i + 1]
    allowed = []
    for a, b in allowed_pairs:
        allowed.append(And(c1 == a, c2 == b))
    s.add(Or(allowed))

# Add required days in each city
required_days = {
    Brussels: 4,
    Bucharest: 3,
    Stuttgart: 4,
    Mykonos: 2,
    Madrid: 2,
    Helsinki: 5,
    Split: 3,
    London: 5
}

for city, count in required_days.items():
    sum_expr = Sum([If(days[d] == city, 1, 0) for d in range(21)])
    s.add(sum_expr == count)

# Add constraints for Madrid conference on days 20 and 21 (indices 19 and 20)
s.add(days[19] == Madrid)
s.add(days[20] == Madrid)

# Add constraint for meeting a friend in Stuttgart between day 1 and day 4 (indices 0 to 3)
stutt_days = [days[i] == Stuttgart for i in range(4)]
s.add(Or(stutt_days))

# Check for a solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(21):
        day_num = i + 1
        city_val = m.evaluate(days[i])
        city_name = city_val.decl().name()
        itinerary.append({day_num: city_name})
    import json
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")