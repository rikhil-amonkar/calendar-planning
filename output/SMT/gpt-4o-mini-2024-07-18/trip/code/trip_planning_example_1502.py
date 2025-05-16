from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 27

# Define days spent in each city
cities = {
    'Santorini': Int('days_in_santorini'),   # 3 days in Santorini
    'Valencia': Int('days_in_valencia'),       # 4 days in Valencia
    'Madrid': Int('days_in_madrid'),           # 2 days in Madrid
    'Seville': Int('days_in_seville'),         # 2 days in Seville
    'Bucharest': Int('days_in_bucharest'),     # 3 days in Bucharest
    'Vienna': Int('days_in_vienna'),           # 4 days in Vienna
    'Riga': Int('days_in_riga'),               # 4 days in Riga
    'Tallinn': Int('days_in_tallinn'),         # 5 days in Tallinn
    'Krakow': Int('days_in_krakow'),           # 5 days in Krakow
    'Frankfurt': Int('days_in_frankfurt'),     # 4 days in Frankfurt
}

# Add constraints on days in cities
solver.add(cities['Santorini'] == 3)
solver.add(cities['Valencia'] == 4)
solver.add(cities['Madrid'] == 2)
solver.add(cities['Seville'] == 2)
solver.add(cities['Bucharest'] == 3)
solver.add(cities['Vienna'] == 4)
solver.add(cities['Riga'] == 4)
solver.add(cities['Tallinn'] == 5)
solver.add(cities['Krakow'] == 5)
solver.add(cities['Frankfurt'] == 4)

# Total days must sum to 27
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 27 days (0-9 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Annual show in Madrid (between day 6 and day 7)
solver.add(days[5] == 2)  # Madrid on day 6
solver.add(days[6] == 2)  # Madrid on day 7

# Wedding in Vienna (between day 3 and day 6)
for i in range(2, 5):  # Days 3, 4, 5
    solver.add(days[i] == 5)  # Vienna

# Meeting friends in Krakow (between day 11 and day 15)
for i in range(10, 15):  # Days 11, 12, 13, 14
    solver.add(days[i] == 8)  # Krakow

# Conference in Riga (on days 20 and 23)
solver.add(days[19] == 6)  # Riga on day 20
solver.add(days[22] == 6)  # Riga on day 23

# Workshop in Tallinn (between day 23 and day 27)
for i in range(22, 27):  # Days 23, 24, 25, 26
    solver.add(days[i] == 7)  # Tallinn

# Define valid city indices
city_indices = {
    'Santorini': 0,
    'Valencia': 1,
    'Madrid': 2,
    'Seville': 3,
    'Bucharest': 4,
    'Vienna': 5,
    'Riga': 6,
    'Tallinn': 7,
    'Krakow': 8,
    'Frankfurt': 9,
}

# Adding constraints for daily assignments (ensuring valid indices)
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Santorini'],
        days[i] == city_indices['Valencia'],
        days[i] == city_indices['Madrid'],
        days[i] == city_indices['Seville'],
        days[i] == city_indices['Bucharest'],
        days[i] == city_indices['Vienna'],
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Tallinn'],
        days[i] == city_indices['Krakow'],
        days[i] == city_indices['Frankfurt'],
    ))

# Define direct flight connections
direct_flights = [
    (5, 4),  # Vienna to Bucharest
    (0, 2),  # Santorini to Madrid
    (3, 1),  # Seville to Valencia
    (5, 3),  # Vienna to Seville
    (2, 1),  # Madrid to Valencia
    (4, 6),  # Bucharest to Riga
    (1, 6),  # Valencia to Bucharest
    (0, 4),  # Santorini to Bucharest
    (5, 1),  # Vienna to Valencia
    (5, 2),  # Vienna to Madrid
    (1, 8),  # Valencia to Krakow
    (1, 9),  # Valencia to Frankfurt
    (8, 9),  # Krakow to Frankfurt
    (3, 6),  # Split to Riga
    (5, 6),  # Vienna to Riga
    (9, 7),  # Frankfurt to Tallinn
    (9, 4),  # Frankfurt to Bucharest
    (2, 4),  # Madrid to Bucharest
    (9, 6),  # Frankfurt to Riga
    (2, 9),  # Madrid to Frankfurt
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
        print(f"Day {i + 1}: City code {city_code} (0=Santorini, 1=Valencia, 2=Madrid, 3=Seville, 4=Bucharest, 5=Vienna, 6=Riga, 7=Tallinn, 8=Krakow, 9=Frankfurt)")
else:
    print("No solution found.")