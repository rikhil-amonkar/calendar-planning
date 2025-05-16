from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 21

# Define the days spent in each city
cities = {
    'Reykjavik': Int('days_in_reykjavik'),  # 7 days
    'Riga': Int('days_in_riga'),            # 2 days
    'Warsaw': Int('days_in_warsaw'),        # 3 days
    'Istanbul': Int('days_in_istanbul'),    # 6 days
    'Krakow': Int('days_in_krakow'),        # 7 days
}

# Add constraints on days spent in each city
solver.add(cities['Reykjavik'] == 7)
solver.add(cities['Riga'] == 2)
solver.add(cities['Warsaw'] == 3)
solver.add(cities['Istanbul'] == 6)
solver.add(cities['Krakow'] == 7)

# Total days must sum to 21
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 21 days (0-4 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meet a friend in Riga (between day 1 and day 2)
solver.add(days[0] == 1)  # Riga (index 1) on day 1
solver.add(days[1] == 1)  # Riga (index 1) on day 2

# Attend a wedding in Istanbul (between day 2 and day 7)
for i in range(1, 6):  # Days 2 to 6
    solver.add(days[i] == 3)  # Istanbul (index 3)

# Define valid city indices
city_indices = {
    'Reykjavik': 0,
    'Riga': 1,
    'Warsaw': 2,
    'Istanbul': 3,
    'Krakow': 4,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Reykjavik'],
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Warsaw'],
        days[i] == city_indices['Istanbul'],
        days[i] == city_indices['Krakow'],
    ))

# Define direct flight connections
direct_flights = [
    (3, 4),  # Istanbul to Krakow
    (2, 0),  # Warsaw to Reykjavik
    (3, 2),  # Istanbul to Warsaw
    (1, 3),  # Riga to Istanbul
    (4, 2),  # Krakow to Warsaw
    (1, 2),  # Riga to Warsaw
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
        print(f"Day {i + 1}: City code {city_code} (0=Reykjavik, 1=Riga, 2=Warsaw, 3=Istanbul, 4=Krakow)")
else:
    print("No solution found.")