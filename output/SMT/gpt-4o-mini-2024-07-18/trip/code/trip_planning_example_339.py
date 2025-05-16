from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 17

# Define the days spent in each city
cities = {
    'Riga': Int('days_in_riga'),         # 7 days
    'Budapest': Int('days_in_budapest'), # 7 days
    'Paris': Int('days_in_paris'),       # 4 days
    'Warsaw': Int('days_in_warsaw'),     # 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Riga'] == 7)
solver.add(cities['Budapest'] == 7)
solver.add(cities['Paris'] == 4)
solver.add(cities['Warsaw'] == 2)

# Total days must sum to 17
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 17 days (0-3 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a wedding in Riga (between day 11 and day 17)
for i in range(10, 17):  # Days 11 to 17
    solver.add(days[i] == 0)  # Riga (index 0)

# Attend an annual show in Warsaw (on day 1 and day 2)
solver.add(days[0] == 3)  # Warsaw (index 3) on day 1
solver.add(days[1] == 3)  # Warsaw (index 3) on day 2

# Define valid city indices
city_indices = {
    'Riga': 0,
    'Budapest': 1,
    'Paris': 2,
    'Warsaw': 3,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Budapest'],
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Warsaw'],
    ))

# Define direct flight connections
direct_flights = [
    (3, 1),  # Warsaw to Budapest
    (3, 0),  # Warsaw to Riga
    (1, 2),  # Budapest to Paris
    (3, 2),  # Warsaw to Paris
    (2, 0),  # Paris to Riga
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
        print(f"Day {i + 1}: City code {city_code} (0=Riga, 1=Budapest, 2=Paris, 3=Warsaw)")
else:
    print("No solution found.")