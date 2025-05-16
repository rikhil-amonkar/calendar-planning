from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 18

# Define the days spent in each city
cities = {
    'Mykonos': Int('days_in_mykonos'),     # 4 days
    'Krakow': Int('days_in_krakow'),       # 5 days
    'Vilnius': Int('days_in_vilnius'),     # 2 days
    'Helsinki': Int('days_in_helsinki'),   # 2 days
    'Dubrovnik': Int('days_in_dubrovnik'), # 3 days
    'Oslo': Int('days_in_oslo'),           # 2 days
    'Madrid': Int('days_in_madrid'),       # 5 days
    'Paris': Int('days_in_paris'),         # 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Mykonos'] == 4)
solver.add(cities['Krakow'] == 5)
solver.add(cities['Vilnius'] == 2)
solver.add(cities['Helsinki'] == 2)
solver.add(cities['Dubrovnik'] == 3)
solver.add(cities['Oslo'] == 2)
solver.add(cities['Madrid'] == 5)
solver.add(cities['Paris'] == 2)

# Total days must sum to 18
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 18 days (0-7 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Annual show in Dubrovnik (from day 2 to day 4)
solver.add(days[1] == 4)  # Dubrovnik (index 4) on day 2
solver.add(days[2] == 4)  # Dubrovnik (index 4) on day 3
solver.add(days[3] == 4)  # Dubrovnik (index 4) on day 4

# Meeting friends in Oslo (between day 1 and day 2)
solver.add(days[0] == 5)  # Oslo (index 5) on day 1
solver.add(days[1] == 5)  # Oslo (index 5) on day 2

# Visiting relatives in Mykonos (between day 15 and day 18)
for i in range(14, total_days):  # Days 15 to 18
    solver.add(days[i] == 0)  # Mykonos (index 0)

# Define valid city indices
city_indices = {
    'Mykonos': 0,
    'Krakow': 1,
    'Vilnius': 2,
    'Helsinki': 3,
    'Dubrovnik': 4,
    'Oslo': 5,
    'Madrid': 6,
    'Paris': 7,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Mykonos'],
        days[i] == city_indices['Krakow'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Dubrovnik'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Madrid'],
        days[i] == city_indices['Paris'],
    ))

# Define direct flight connections
direct_flights = [
    (5, 1),  # Oslo to Krakow
    (5, 7),  # Oslo to Paris
    (7, 6),  # Paris to Madrid
    (3, 2),  # Helsinki to Vilnius
    (5, 6),  # Oslo to Madrid
    (5, 3),  # Oslo to Helsinki
    (3, 1),  # Helsinki to Krakow
    (4, 3),  # Dubrovnik to Helsinki
    (4, 6),  # Dubrovnik to Madrid
    (5, 4),  # Oslo to Dubrovnik
    (1, 7),  # Krakow to Paris
    (6, 7),  # Madrid to Paris
    (1, 2),  # Krakow to Vilnius
    (2, 7),  # Vilnius to Paris
    (3, 6),  # Helsinki to Madrid
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
        print(f"Day {i + 1}: City code {city_code} (0=Mykonos, 1=Krakow, 2=Vilnius, 3=Helsinki, 4=Dubrovnik, 5=Oslo, 6=Madrid, 7=Paris)")
else:
    print("No solution found.")