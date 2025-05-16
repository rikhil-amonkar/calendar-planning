from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 25

# Define the days spent in each city
cities = {
    'Oslo': Int('days_in_oslo'),           # 2 days
    'Helsinki': Int('days_in_helsinki'),   # 2 days
    'Edinburgh': Int('days_in_edinburgh'), # 3 days
    'Riga': Int('days_in_riga'),           # 2 days
    'Tallinn': Int('days_in_tallinn'),     # 5 days
    'Budapest': Int('days_in_budapest'),   # 5 days
    'Vilnius': Int('days_in_vilnius'),     # 5 days
    'Porto': Int('days_in_porto'),         # 5 days
    'Geneva': Int('days_in_geneva'),       # 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Oslo'] == 2)
solver.add(cities['Helsinki'] == 2)
solver.add(cities['Edinburgh'] == 3)
solver.add(cities['Riga'] == 2)
solver.add(cities['Tallinn'] == 5)
solver.add(cities['Budapest'] == 5)
solver.add(cities['Vilnius'] == 5)
solver.add(cities['Porto'] == 5)
solver.add(cities['Geneva'] == 4)

# Total days must sum to 25
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 25 days (0-8 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meeting a friend in Oslo (on day 24 and day 25)
solver.add(days[23] == 0)  # Oslo (index 0) on day 24
solver.add(days[24] == 0)  # Oslo (index 0) on day 25

# Attend a wedding in Tallinn (between day 4 and day 8)
for i in range(3, 8):  # Days 4 to 8
    solver.add(days[i] == 4)  # Tallinn (index 4)

# Define valid city indices
city_indices = {
    'Oslo': 0,
    'Helsinki': 1,
    'Edinburgh': 2,
    'Riga': 3,
    'Tallinn': 4,
    'Budapest': 5,
    'Vilnius': 6,
    'Porto': 7,
    'Geneva': 8,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Edinburgh'],
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Tallinn'],
        days[i] == city_indices['Budapest'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Porto'],
        days[i] == city_indices['Geneva'],
    ))

# Define direct flight connections
direct_flights = [
    (7, 0),  # Porto to Oslo
    (2, 5),  # Edinburgh to Budapest
    (2, 8),  # Edinburgh to Geneva
    (3, 4),  # Riga to Tallinn
    (2, 7),  # Edinburgh to Porto
    (6, 1),  # Vilnius to Helsinki
    (4, 0),  # Tallinn to Oslo
    (4, 1),  # Tallinn to Helsinki
    (8, 0),  # Geneva to Oslo
    (5, 0),  # Budapest to Oslo
    (1, 2),  # Helsinki to Edinburgh
    (1, 3),  # Helsinki to Riga
    (5, 8),  # Budapest to Geneva
    (1, 5),  # Helsinki to Budapest
    (1, 0),  # Helsinki to Oslo
    (3, 6),  # Riga to Vilnius
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
        print(f"Day {i + 1}: City code {city_code} (0=Oslo, 1=Helsinki, 2=Edinburgh, 3=Riga, 4=Tallinn, 5=Budapest, 6=Vilnius, 7=Porto, 8=Geneva)")
else:
    print("No solution found.")