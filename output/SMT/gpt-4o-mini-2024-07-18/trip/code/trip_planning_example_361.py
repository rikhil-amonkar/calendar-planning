from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 15

# Define the days spent in each city
cities = {
    'Paris': Int('days_in_paris'),           # 6 days
    'Madrid': Int('days_in_madrid'),         # 7 days
    'Bucharest': Int('days_in_bucharest'),   # 2 days
    'Seville': Int('days_in_seville'),       # 3 days
}

# Add constraints on the number of days spent in each city
solver.add(cities['Paris'] == 6)
solver.add(cities['Madrid'] == 7)
solver.add(cities['Bucharest'] == 2)
solver.add(cities['Seville'] == 3)

# Total days must sum to 15
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 15 days (0-3 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Annual show in Madrid (between day 1 and day 7)
for i in range(0, 7):  # Days 1 to 7
    solver.add(days[i] == 1)  # Madrid

# Visiting relatives in Bucharest (between day 14 and day 15)
solver.add(days[13] == 2)  # Bucharest on day 14
solver.add(days[14] == 2)  # Bucharest on day 15

# Define valid city indices
city_indices = {
    'Paris': 0,
    'Madrid': 1,
    'Bucharest': 2,
    'Seville': 3,
}

# Ensure only valid city indices for each day
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Madrid'],
        days[i] == city_indices['Bucharest'],
        days[i] == city_indices['Seville'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 2),  # Paris to Bucharest
    (3, 0),  # Seville to Paris
    (1, 2),  # Madrid to Bucharest
    (1, 0),  # Madrid to Paris
    (1, 3),  # Madrid to Seville
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
        print(f"Day {i + 1}: City code {city_code} (0=Paris, 1=Madrid, 2=Bucharest, 3=Seville)")
else:
    print("No solution found.")