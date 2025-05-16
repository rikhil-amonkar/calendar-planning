from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 14

# Define the days spent in each city
cities = {
    'Helsinki': Int('days_in_helsinki'),     # 2 days
    'Warsaw': Int('days_in_warsaw'),         # 3 days
    'Madrid': Int('days_in_madrid'),         # 4 days
    'Split': Int('days_in_split'),           # 4 days
    'Reykjavik': Int('days_in_reykjavik'),   # 2 days
    'Budapest': Int('days_in_budapest'),     # 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Helsinki'] == 2)
solver.add(cities['Warsaw'] == 3)
solver.add(cities['Madrid'] == 4)
solver.add(cities['Split'] == 4)
solver.add(cities['Reykjavik'] == 2)
solver.add(cities['Budapest'] == 4)

# Total days must sum to 14
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 14 days (0-5 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a workshop in Helsinki (on day 1 and day 2)
solver.add(days[0] == 0)  # Helsinki (index 0) on day 1
solver.add(days[1] == 0)  # Helsinki (index 0) on day 2

# Visit relatives in Warsaw (between day 9 and day 11)
for i in range(8, 11):  # Days 9 to 11
    solver.add(days[i] == 1)  # Warsaw (index 1)

# Meet a friend in Reykjavik (between day 8 and day 9)
solver.add(days[7] == 4)  # Reykjavik (index 4) on day 8

# Define valid city indices
city_indices = {
    'Helsinki': 0,
    'Warsaw': 1,
    'Madrid': 2,
    'Split': 3,
    'Reykjavik': 4,
    'Budapest': 5,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Warsaw'],
        days[i] == city_indices['Madrid'],
        days[i] == city_indices['Split'],
        days[i] == city_indices['Reykjavik'],
        days[i] == city_indices['Budapest'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 4),  # Helsinki to Reykjavik
    (5, 1),  # Budapest to Warsaw
    (2, 3),  # Madrid to Split
    (0, 3),  # Helsinki to Split
    (0, 2),  # Helsinki to Madrid
    (0, 5),  # Helsinki to Budapest
    (4, 1),  # Reykjavik to Warsaw
    (0, 1),  # Helsinki to Warsaw
    (2, 5),  # Madrid to Budapest
    (5, 4),  # Budapest to Reykjavik
    (2, 1),  # Madrid to Warsaw
    (1, 3),  # Warsaw to Split
    (4, 3),  # Reykjavik to Split
    (4, 2),  # Reykjavik to Madrid
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
        print(f"Day {i + 1}: City code {city_code} (0=Helsinki, 1=Warsaw, 2=Madrid, 3=Split, 4=Reykjavik, 5=Budapest)")
else:
    print("No solution found.")