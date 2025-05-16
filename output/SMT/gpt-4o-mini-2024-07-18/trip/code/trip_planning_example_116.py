from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 18

# Define the days spent in each city
cities = {
    'Split': Int('days_in_split'),      # 6 days
    'Santorini': Int('days_in_santorini'), # 7 days
    'London': Int('days_in_london'),     # 7 days
}

# Add constraints on days spent in each city
solver.add(cities['Split'] == 6)
solver.add(cities['Santorini'] == 7)
solver.add(cities['London'] == 7)

# Total days must sum to 18
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 18 days (0-2 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a conference in Santorini (on day 12 and day 18)
solver.add(days[11] == 1)  # Santorini (index 1) on day 12
solver.add(days[17] == 1)  # Santorini (index 1) on day 18

# Define valid city indices
city_indices = {
    'Split': 0,
    'Santorini': 1,
    'London': 2,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Split'],
        days[i] == city_indices['Santorini'],
        days[i] == city_indices['London'],
    ))

# Define direct flight connections
direct_flights = [
    (2, 1),  # London to Santorini
    (0, 2),  # Split to London
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
        print(f"Day {i + 1}: City code {city_code} (0=Split, 1=Santorini, 2=London)")
else:
    print("No solution found.")