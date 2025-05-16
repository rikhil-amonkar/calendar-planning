from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 14

# Define the days spent in each city
cities = {
    'Split': Int('days_in_split'),        # 5 days
    'Vilnius': Int('days_in_vilnius'),    # 4 days
    'Santorini': Int('days_in_santorini'),# 2 days
    'Madrid': Int('days_in_madrid'),      # 6 days
}

# Add constraints on days spent in each city
solver.add(cities['Split'] == 5)
solver.add(cities['Vilnius'] == 4)
solver.add(cities['Santorini'] == 2)
solver.add(cities['Madrid'] == 6)

# Total days must sum to 14
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 14 days (0-3 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a conference in Santorini (on day 13 and day 14)
solver.add(days[12] == 2)  # Santorini (index 2) on day 13
solver.add(days[13] == 2)  # Santorini (index 2) on day 14

# Define valid city indices
city_indices = {
    'Split': 0,
    'Vilnius': 1,
    'Santorini': 2,
    'Madrid': 3,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Split'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Santorini'],
        days[i] == city_indices['Madrid'],
    ))

# Define direct flight connections
direct_flights = [
    (1, 0),  # Vilnius to Split
    (0, 3),  # Split to Madrid
    (3, 2),  # Madrid to Santorini
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
        print(f"Day {i + 1}: City code {city_code} (0=Split, 1=Vilnius, 2=Santorini, 3=Madrid)")
else:
    print("No solution found.")