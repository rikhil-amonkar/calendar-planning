from z3 import *

# Define cities with indices
cities = {
    'Geneva': 0,
    'Munich': 1,
    'Valencia': 2,
    'Bucharest': 3,
    'Stuttgart': 4,
    'Hamburg': 5,  # Not used but part of problem statement
    'Mykonos': 6    # Not used but part of problem statement
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items() if k in ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']}

# Required days per city
required_days = {
    cities['Geneva']: 4,
    cities['Munich']: 7,
    cities['Valencia']: 6,
    cities['Bucharest']: 2,
    cities['Stuttgart']: 2
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 1), (1, 0),  # Geneva <-> Munich
    (1, 2), (2, 1),  # Munich <-> Valencia
    (3, 2), (2, 3),  # Bucharest <-> Valencia
    (1, 3), (3, 1),  # Munich <-> Bucharest
    (2, 4), (4, 2),  # Valencia <-> Stuttgart
    (0, 2), (2, 0)   # Geneva <-> Valencia
]

# Create solver
s = Solver()

# Day variables: 1 to 17 (indices 0-16)
days = [Int(f'day_{i}') for i in range(17)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in required_days.keys()]))

# Fixed days in Geneva (days 1-4, indices 0-3)
for i in range(4):
    s.add(days[i] == cities['Geneva'])

# Munich must be visited for 7 days between day 4 and day 10 (indices 3-9)
# This creates a conflict with Geneva on day 4 (index 3)
munich_days = [days[i] == cities['Munich'] for i in range(3, 10)]
s.add(Sum([If(md, 1, 0) for md in munich_days]) == 7)

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 17):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(17):
        day = i + 1
        city = inv_cities.get(schedule[i].as_long(), 'Unknown')
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")