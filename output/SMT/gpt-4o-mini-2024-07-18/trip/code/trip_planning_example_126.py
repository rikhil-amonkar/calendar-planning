from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 11

# Define the days spent in each city
cities = {
    'Seville': Int('days_in_seville'),
    'Paris': Int('days_in_paris'),
    'Krakow': Int('days_in_krakow'),
}

# Constraints on days in cities
solver.add(cities['Seville'] == 6)              # 6 days in Seville
solver.add(cities['Paris'] == 2)                # 2 days in Paris
solver.add(cities['Krakow'] == 5)               # 5 days in Krakow

# Total days must sum to 11
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 11 days (0-2 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Workshop in Krakow (between day 1 and day 5)
for i in range(5):  # Days 1 to 5
    solver.add(days[i] == 2)  # Krakow on days 1 to 5

# Define valid city indices
city_indices = {
    'Seville': 0,
    'Paris': 1,
    'Krakow': 2,
}

# Adding constraints for daily assignments
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Seville'],
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Krakow'],
    ))

# Define direct flight connections
direct_flights = [
    (2, 1),  # Krakow to Paris
    (1, 0),  # Paris to Seville
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
        print(f"Day {i + 1}: City code {city_code} (0=Seville, 1=Paris, 2=Krakow)")
else:
    print("No solution found.")