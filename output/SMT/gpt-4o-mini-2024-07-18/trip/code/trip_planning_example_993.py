from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 15

# Define the days spent in each city
cities = {
    'Riga': Int('days_in_riga'),           # 2 days
    'Frankfurt': Int('days_in_frankfurt'), # 3 days
    'Amsterdam': Int('days_in_amsterdam'), # 2 days
    'Vilnius': Int('days_in_vilnius'),     # 5 days
    'London': Int('days_in_london'),       # 2 days
    'Stockholm': Int('days_in_stockholm'), # 3 days
    'Bucharest': Int('days_in_bucharest'), # 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Riga'] == 2)
solver.add(cities['Frankfurt'] == 3)
solver.add(cities['Amsterdam'] == 2)
solver.add(cities['Vilnius'] == 5)
solver.add(cities['London'] == 2)
solver.add(cities['Stockholm'] == 3)
solver.add(cities['Bucharest'] == 4)

# Total days must sum to 15
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 15 days (0-6 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meeting a friend in Amsterdam (between day 2 and day 3)
solver.add(days[1] == 2)  # Amsterdam on day 2
solver.add(days[2] == 2)  # Amsterdam on day 3

# Attend a workshop in Vilnius (between day 7 and day 11)
for i in range(6, 11):  # Days 7 to 11
    solver.add(days[i] == 3)  # Vilnius

# Attend a wedding in Stockholm (between day 13 and day 15)
for i in range(12, 15):  # Days 13, 14
    solver.add(days[i] == 6)  # Stockholm
solver.add(days[14] == 6)  # Stockholm on day 15

# Define valid city indices
city_indices = {
    'Riga': 0,
    'Frankfurt': 1,
    'Amsterdam': 2,
    'Vilnius': 3,
    'London': 4,
    'Stockholm': 5,
    'Bucharest': 6,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Frankfurt'],
        days[i] == city_indices['Amsterdam'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['London'],
        days[i] == city_indices['Stockholm'],
        days[i] == city_indices['Bucharest'],
    ))

# Define direct flight connections
direct_flights = [
    (4, 2),  # London to Amsterdam
    (3, 1),  # Vilnius to Frankfurt
    (0, 3),  # Riga to Vilnius
    (0, 5),  # Riga to Stockholm
    (4, 6),  # London to Bucharest
    (2, 5),  # Amsterdam to Stockholm
    (2, 1),  # Amsterdam to Frankfurt
    (1, 5),  # Frankfurt to Stockholm
    (6, 0),  # Bucharest to Riga
    (2, 0),  # Amsterdam to Riga
    (2, 6),  # Amsterdam to Bucharest
    (0, 1),  # Riga to Frankfurt
    (6, 1),  # Bucharest to Frankfurt
    (4, 1),  # London to Frankfurt
    (4, 5),  # London to Stockholm
    (2, 3),  # Amsterdam to Vilnius
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
        print(f"Day {i + 1}: City code {city_code} (0=Riga, 1=Frankfurt, 2=Amsterdam, 3=Vilnius, 4=London, 5=Stockholm, 6=Bucharest)")
else:
    print("No solution found.")