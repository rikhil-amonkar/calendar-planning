from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 10

# Define the number of days spent in each city
cities = {
    'Krakow': Int('days_in_krakow'),    # 2 days
    'Dubrovnik': Int('days_in_dubrovnik'),  # 7 days
    'Frankfurt': Int('days_in_frankfurt'),  # 3 days
}

# Add constraints on days spent in each city
solver.add(cities['Krakow'] == 2)
solver.add(cities['Dubrovnik'] == 7)
solver.add(cities['Frankfurt'] == 3)

# Total days must sum to 10
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 10 days (0-2 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a wedding in Krakow (on day 9 and day 10)
solver.add(days[8] == 0)  # Krakow (index 0) on day 9
solver.add(days[9] == 0)  # Krakow (index 0) on day 10

# Define valid city indices
city_indices = {
    'Krakow': 0,
    'Dubrovnik': 1,
    'Frankfurt': 2,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Krakow'],
        days[i] == city_indices['Dubrovnik'],
        days[i] == city_indices['Frankfurt'],
    ))

# Define direct flight connections
direct_flights = [
    (2, 0),  # Frankfurt to Krakow
    (1, 2),  # Dubrovnik to Frankfurt
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
        print(f"Day {i + 1}: City code {city_code} (0=Krakow, 1=Dubrovnik, 2=Frankfurt)")
else:
    print("No solution found.")