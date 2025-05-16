from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 18

# Define the days spent in each city
cities = {
    'Krakow': Int('days_in_krakow'),
    'Frankfurt': Int('days_in_frankfurt'),
    'Oslo': Int('days_in_oslo'),
    'Dubrovnik': Int('days_in_dubrovnik'),
    'Naples': Int('days_in_naples'),
}

# Constraints on days in cities
solver.add(cities['Krakow'] == 5)      # 5 days in Krakow
solver.add(cities['Frankfurt'] == 4)    # 4 days in Frankfurt
solver.add(cities['Oslo'] == 3)         # 3 days in Oslo
solver.add(cities['Dubrovnik'] == 5)    # 5 days in Dubrovnik
solver.add(cities['Naples'] == 5)       # 5 days in Naples

# Total days must sum to 18
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 18 days (0-4 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Visiting relatives in Oslo (between day 16 and day 18)
for i in range(15, 18):
    solver.add(days[i] == 2)  # Oslo on days 16 to 18

# Meeting friends in Dubrovnik (between day 5 and day 9)
for i in range(4, 9):
    solver.add(days[i] == 3)  # Dubrovnik on days 5 to 9

# Define valid city indices
city_indices = {
    'Krakow': 0,
    'Frankfurt': 1,
    'Oslo': 2,
    'Dubrovnik': 3,
    'Naples': 4,
}

# Adding constraints for daily assignments
# Ensure only valid city indices for each day
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Krakow'],
        days[i] == city_indices['Frankfurt'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Dubrovnik'],
        days[i] == city_indices['Naples'],
    ))

# Define direct flight connections
direct_flights = [
    (3, 2),  # Dubrovnik to Oslo
    (1, 0),  # Frankfurt to Krakow
    (1, 2),  # Frankfurt to Oslo
    (3, 1),  # Dubrovnik to Frankfurt
    (0, 2),  # Krakow to Oslo
    (4, 2),  # Naples to Oslo
    (4, 3),  # Naples to Dubrovnik
    (4, 1),  # Naples to Frankfurt
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
        print(f"Day {i + 1}: City code {city_code} (0=Krakow, 1=Frankfurt, 2=Oslo, 3=Dubrovnik, 4=Naples)")
else:
    print("No solution found.")