from z3 import *

# Define cities with indices
cities = {
    'Stuttgart': 0,
    'Seville': 1,
    'Manchester': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Stuttgart']: 6,
    cities['Seville']: 7,
    cities['Manchester']: 4
}

# Allowed direct flights (from, to)
allowed_flights = [
    (2, 1), (1, 2),  # Manchester <-> Seville
    (0, 2), (2, 0)   # Stuttgart <-> Manchester
]

# Create solver
s = Solver()

# Day variables: 1 to 15 (indices 0-14)
days = [Int(f'day_{i}') for i in range(15)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Stuttgart must be visited for 6 days between day 1 and 6 (indices 0-5)
stuttgart_in_period = [days[i] == cities['Stuttgart'] for i in range(6)]
s.add(Sum([If(cond, 1, 0) for cond in stuttgart_in_period]) >= 1  # At least 1 day in period
s.add(Sum([If(d == cities['Stuttgart'], 1, 0) for d in days]) == 6  # Total Stuttgart days

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 15):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(15):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")