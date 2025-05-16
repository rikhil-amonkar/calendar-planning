from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 18

# Define the days spent in each city
cities = {
    'Helsinki': Int('days_in_helsinki'),  # 4 days
    'Valencia': Int('days_in_valencia'),  # 5 days
    'Dubrovnik': Int('days_in_dubrovnik'),# 4 days
    'Porto': Int('days_in_porto'),        # 3 days
    'Prague': Int('days_in_prague'),      # 3 days
    'Reykjavik': Int('days_in_reykjavik'),# 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Helsinki'] == 4)
solver.add(cities['Valencia'] == 5)
solver.add(cities['Dubrovnik'] == 4)
solver.add(cities['Porto'] == 3)
solver.add(cities['Prague'] == 3)
solver.add(cities['Reykjavik'] == 4)

# Total days must sum to 18
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 18 days (0-5 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meet a friend in Porto (between day 16 and 18)
solver.add(days[15] == 3)  # Porto (index 3) on day 16
solver.add(days[16] == 3)  # Porto (index 3) on day 17

# Define valid city indices
city_indices = {
    'Helsinki': 0,
    'Valencia': 1,
    'Dubrovnik': 2,
    'Porto': 3,
    'Prague': 4,
    'Reykjavik': 5,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Valencia'],
        days[i] == city_indices['Dubrovnik'],
        days[i] == city_indices['Porto'],
        days[i] == city_indices['Prague'],
        days[i] == city_indices['Reykjavik'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 4),  # Helsinki to Prague
    (4, 1),  # Prague to Valencia
    (1, 3),  # Valencia to Porto
    (0, 5),  # Helsinki to Reykjavik
    (2, 0),  # Dubrovnik to Helsinki
    (5, 4),  # Reykjavik to Prague
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
        print(f"Day {i + 1}: City code {city_code} (0=Helsinki, 1=Valencia, 2=Dubrovnik, 3=Porto, 4=Prague, 5=Reykjavik)")
else:
    print("No solution found.")