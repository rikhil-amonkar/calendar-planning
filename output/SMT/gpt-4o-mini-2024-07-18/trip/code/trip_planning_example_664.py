from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 18

# Define the days spent in each city
cities = {
    'Tallinn': Int('days_in_tallinn'),       # 2 days
    'Bucharest': Int('days_in_bucharest'),   # 4 days
    'Seville': Int('days_in_seville'),       # 5 days
    'Stockholm': Int('days_in_stockholm'),   # 5 days
    'Munich': Int('days_in_munich'),         # 5 days
    'Milan': Int('days_in_milan'),           # 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Tallinn'] == 2)
solver.add(cities['Bucharest'] == 4)
solver.add(cities['Seville'] == 5)
solver.add(cities['Stockholm'] == 5)
solver.add(cities['Munich'] == 5)
solver.add(cities['Milan'] == 2)

# Total days must sum to 18
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 18 days (0-5 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Visiting relatives in Bucharest (between day 1 and day 4)
for i in range(0, 4):  # Days 1 to 4
    solver.add(days[i] == 1)  # Bucharest

# Attend a wedding in Munich (between day 4 and day 8)
for i in range(3, 8):  # Days 4 to 7
    solver.add(days[i] == 4)  # Munich

# Meeting friends in Seville (between day 8 and day 12)
for i in range(7, 12):  # Days 8 to 11
    solver.add(days[i] == 2)  # Seville

# Define valid city indices
city_indices = {
    'Tallinn': 0,
    'Bucharest': 1,
    'Seville': 2,
    'Stockholm': 3,
    'Munich': 4,
    'Milan': 5,
}

# Ensure only valid city indices for each day
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Tallinn'],
        days[i] == city_indices['Bucharest'],
        days[i] == city_indices['Seville'],
        days[i] == city_indices['Stockholm'],
        days[i] == city_indices['Munich'],
        days[i] == city_indices['Milan'],
    ))

# Define direct flight connections
direct_flights = [
    (5, 3),  # Milan to Stockholm
    (4, 3),  # Munich to Stockholm
    (1, 4),  # Bucharest to Munich
    (4, 2),  # Munich to Seville
    (3, 0),  # Stockholm to Tallinn
    (4, 5),  # Munich to Milan
    (4, 0),  # Munich to Tallinn
    (2, 5),  # Seville to Milan
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
        print(f"Day {i + 1}: City code {city_code} (0=Tallinn, 1=Bucharest, 2=Seville, 3=Stockholm, 4=Munich, 5=Milan)")
else:
    print("No solution found.")