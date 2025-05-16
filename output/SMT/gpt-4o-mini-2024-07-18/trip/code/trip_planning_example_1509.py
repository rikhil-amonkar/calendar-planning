from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 25

# Define the days spent in each city
cities = {
    'Paris': Int('days_in_paris'),         # 5 days
    'Warsaw': Int('days_in_warsaw'),       # 2 days
    'Krakow': Int('days_in_krakow'),       # 2 days
    'Tallinn': Int('days_in_tallinn'),     # 2 days
    'Riga': Int('days_in_riga'),           # 2 days
    'Copenhagen': Int('days_in_copenhagen'),  # 5 days
    'Helsinki': Int('days_in_helsinki'),    # 5 days
    'Oslo': Int('days_in_oslo'),            # 5 days
    'Santorini': Int('days_in_santorini'),  # 2 days
    'Lyon': Int('days_in_lyon')              # 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Paris'] == 5)
solver.add(cities['Warsaw'] == 2)
solver.add(cities['Krakow'] == 2)
solver.add(cities['Tallinn'] == 2)
solver.add(cities['Riga'] == 2)
solver.add(cities['Copenhagen'] == 5)
solver.add(cities['Helsinki'] == 5)
solver.add(cities['Oslo'] == 5)
solver.add(cities['Santorini'] == 2)
solver.add(cities['Lyon'] == 4)

# Total days must sum to 25
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 25 days (0-9 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meet friends in Paris (between day 4 and day 8)
for i in range(3, 8):  # Days 4 to 8
    solver.add(days[i] == 0)  # Paris (index 0)

# Attend a workshop in Krakow (between day 17 and day 18)
solver.add(days[16] == 2)  # Krakow (index 2) on day 17
solver.add(days[17] == 2)  # Krakow (index 2) on day 18

# Attend a wedding in Riga (between day 23 and day 24)
solver.add(days[22] == 4)  # Riga (index 4) on day 23
solver.add(days[23] == 4)  # Riga (index 4) on day 24

# Meet a friend in Helsinki (between day 18 and day 22)
for i in range(17, 22):  # Days 18 to 21
    solver.add(days[i] == 6)  # Helsinki (index 6)

# Visit relatives in Santorini (on day 12 and day 13)
solver.add(days[11] == 8)  # Santorini (index 8)
solver.add(days[12] == 8)  # Santorini (index 8)

# Define valid city indices
city_indices = {
    'Paris': 0,
    'Warsaw': 1,
    'Krakow': 2,
    'Tallinn': 3,
    'Riga': 4,
    'Copenhagen': 5,
    'Helsinki': 6,
    'Oslo': 7,
    'Santorini': 8,
    'Lyon': 9
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Warsaw'],
        days[i] == city_indices['Krakow'],
        days[i] == city_indices['Tallinn'],
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Copenhagen'],
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Santorini'],
        days[i] == city_indices['Lyon'],
    ))

# Define direct flight connections
direct_flights = [
    (1, 4),  # Warsaw to Riga
    (1, 3),  # Warsaw to Tallinn
    (5, 6),  # Copenhagen to Helsinki
    (9, 0),  # Lyon to Paris
    (5, 0),  # Copenhagen to Paris
    (5, 1),  # Copenhagen to Warsaw
    (7, 3),  # Lyon to Oslo
    (0, 7),  # Paris to Oslo
    (0, 4),  # Paris to Riga
    (2, 3),  # Krakow to Helsinki
    (0, 3),  # Paris to Tallinn
    (7, 4),  # Oslo to Riga
    (2, 1),  # Krakow to Warsaw
    (0, 6),  # Paris to Helsinki
    (5, 8),  # Copenhagen to Santorini
    (6, 1),  # Helsinki to Warsaw
    (6, 4),  # Helsinki to Riga
    (5, 2),  # Copenhagen to Krakow
    (5, 4),  # Copenhagen to Riga
    (0, 2),  # Paris to Krakow
    (5, 7),  # Copenhagen to Oslo
    (7, 3),  # Oslo to Tallinn
    (7, 6),  # Oslo to Helsinki
    (5, 3),  # Copenhagen to Tallinn
    (7, 2),  # Oslo to Krakow
    (4, 3)   # Riga to Tallinn
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
        print(f"Day {i + 1}: City code {city_code} (0=Paris, 1=Warsaw, 2=Krakow, 3=Tallinn, 4=Riga, 5=Copenhagen, 6=Helsinki, 7=Oslo, 8=Santorini, 9=Lyon)")
else:
    print("No solution found.")