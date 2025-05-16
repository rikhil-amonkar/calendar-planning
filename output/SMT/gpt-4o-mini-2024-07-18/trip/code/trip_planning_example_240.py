from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 12

# Define the days spent in each city
cities = {
    'Prague': Int('days_in_prague'),       # 2 days
    'Berlin': Int('days_in_berlin'),       # 3 days
    'Tallinn': Int('days_in_tallinn'),     # 5 days
    'Stockholm': Int('days_in_stockholm'), # 5 days
}

# Add constraints on days spent in each city
solver.add(cities['Prague'] == 2)
solver.add(cities['Berlin'] == 3)
solver.add(cities['Tallinn'] == 5)
solver.add(cities['Stockholm'] == 5)

# Total days must sum to 12
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 12 days (0-3 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a conference in Berlin (on day 6 and day 8)
solver.add(days[5] == 1)  # Berlin (index 1) on day 6
solver.add(days[7] == 1)  # Berlin (index 1) on day 8

# Visit relatives in Tallinn (between day 8 and day 12)
for i in range(7, 12):  # Days 8 to 11
    solver.add(days[i] == 2)  # Tallinn (index 2)

# Define valid city indices
city_indices = {
    'Prague': 0,
    'Berlin': 1,
    'Tallinn': 2,
    'Stockholm': 3,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Prague'],
        days[i] == city_indices['Berlin'],
        days[i] == city_indices['Tallinn'],
        days[i] == city_indices['Stockholm'],
    ))

# Define direct flight connections
direct_flights = [
    (1, 2),  # Berlin to Tallinn
    (0, 2),  # Prague to Tallinn
    (3, 2),  # Stockholm to Tallinn
    (0, 3),  # Prague to Stockholm
    (3, 1),  # Stockholm to Berlin
]

# Add constraints based on direct flights
for i in range(total_days - 1):
    for src, dst in direct_flights:
        solver.add(If(days[i] == src, days[i + 1] == dst, True))

# Solve the scheduling problem
if solver.check() == sat:
    model = solver.model()
    print("Schedule:")
    for i in range(total_days):
        city_code = model[days[i]].as_long()
        print(f"Day {i + 1}: City code {city_code} (0=Prague, 1=Berlin, 2=Tallinn, 3=Stockholm)")
else:
    print("No solution found.")