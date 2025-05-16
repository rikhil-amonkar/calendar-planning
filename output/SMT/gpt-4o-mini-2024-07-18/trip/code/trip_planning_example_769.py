from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 16

# Define the days spent in each city
cities = {
    'Porto': Int('days_in_porto'),         # 5 days
    'Prague': Int('days_in_prague'),       # 4 days
    'Reykjavik': Int('days_in_reykjavik'), # 4 days
    'Santorini': Int('days_in_santorini'), # 2 days
    'Amsterdam': Int('days_in_amsterdam'), # 2 days
    'Munich': Int('days_in_munich'),       # 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Porto'] == 5)
solver.add(cities['Prague'] == 4)
solver.add(cities['Reykjavik'] == 4)
solver.add(cities['Santorini'] == 2)
solver.add(cities['Amsterdam'] == 2)
solver.add(cities['Munich'] == 4)

# Total days must sum to 16
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 16 days (0-5 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a wedding in Reykjavik (between day 4 and day 7)
for i in range(3, 7):  # Days 4 to 6
    solver.add(days[i] == 2)  # Reykjavik (index 2)

# Meet a friend in Munich (between day 7 and day 10)
for i in range(6, 10):  # Days 7 to 9
    solver.add(days[i] == 5)  # Munich (index 5)

# Attend a conference in Amsterdam (on day 14 and day 15)
solver.add(days[13] == 4)  # Amsterdam (index 4) on day 14
solver.add(days[14] == 4)  # Amsterdam (index 4) on day 15

# Define valid city indices
city_indices = {
    'Porto': 0,
    'Prague': 1,
    'Reykjavik': 2,
    'Santorini': 3,
    'Amsterdam': 4,
    'Munich': 5,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Porto'],
        days[i] == city_indices['Prague'],
        days[i] == city_indices['Reykjavik'],
        days[i] == city_indices['Santorini'],
        days[i] == city_indices['Amsterdam'],
        days[i] == city_indices['Munich'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 4),  # Porto to Amsterdam
    (5, 4),  # Munich to Amsterdam
    (2, 4),  # Reykjavik to Amsterdam
    (5, 0),  # Munich to Porto
    (1, 2),  # Prague to Reykjavik
    (2, 5),  # Reykjavik to Munich
    (4, 3),  # Amsterdam to Santorini
    (1, 4),  # Prague to Amsterdam
    (1, 5),  # Prague to Munich
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
        print(f"Day {i + 1}: City code {city_code} (0=Porto, 1=Prague, 2=Reykjavik, 3=Santorini, 4=Amsterdam, 5=Munich)")
else:
    print("No solution found.")