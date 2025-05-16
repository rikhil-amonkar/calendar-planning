from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 8

# Define the days spent in each city
cities = {
    'Prague': Int('days_in_prague'),       # 4 days
    'Stuttgart': Int('days_in_stuttgart'), # 2 days
    'Split': Int('days_in_split'),         # 2 days
    'Krakow': Int('days_in_krakow'),       # 2 days
    'Florence': Int('days_in_florence'),   # 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Prague'] == 4)
solver.add(cities['Stuttgart'] == 2)
solver.add(cities['Split'] == 2)
solver.add(cities['Krakow'] == 2)
solver.add(cities['Florence'] == 2)

# Total days must sum to 8
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 8 days (0-4 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a wedding in Stuttgart (between day 2 and day 3)
solver.add(days[1] == 1)  # Stuttgart on day 2
solver.add(days[2] == 1)  # Stuttgart on day 3

# Meet friends in Split (between day 3 and day 4)
solver.add(days[2] == 2)  # Split on day 3
solver.add(days[3] == 2)  # Split on day 4

# Define valid city indices
city_indices = {
    'Prague': 0,
    'Stuttgart': 1,
    'Split': 2,
    'Krakow': 3,
    'Florence': 4,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Prague'],
        days[i] == city_indices['Stuttgart'],
        days[i] == city_indices['Split'],
        days[i] == city_indices['Krakow'],
        days[i] == city_indices['Florence'],
    ))

# Define direct flight connections
direct_flights = [
    (1, 2),  # Stuttgart to Split
    (0, 4),  # Prague to Florence
    (3, 1),  # Krakow to Stuttgart
    (3, 2),  # Krakow to Split
    (2, 0),  # Split to Prague
    (3, 0),  # Krakow to Prague
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
        print(f"Day {i + 1}: City code {city_code} (0=Prague, 1=Stuttgart, 2=Split, 3=Krakow, 4=Florence)")
else:
    print("No solution found.")