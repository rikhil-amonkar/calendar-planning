from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 16

# Define the days spent in each city
cities = {
    'Split': Int('days_in_split'),       # 5 days
    'Oslo': Int('days_in_oslo'),         # 2 days
    'London': Int('days_in_london'),     # 7 days
    'Porto': Int('days_in_porto'),       # 5 days
}

# Add constraints on days spent in each city
solver.add(cities['Split'] == 5)
solver.add(cities['Oslo'] == 2)
solver.add(cities['London'] == 7)
solver.add(cities['Porto'] == 5)

# Total days must sum to 16
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 16 days (0-3 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a show in Split (between day 7 and day 11)
for i in range(6, 11):  # Days 7 to 11
    solver.add(days[i] == 0)  # Split (index 0)

# Visit relatives in London (between day 1 and day 7)
for i in range(0, 6):  # Days 1 to 6
    solver.add(days[i] == 1)  # London (index 1)

# Define valid city indices
city_indices = {
    'Split': 0,
    'Oslo': 1,
    'London': 2,
    'Porto': 3,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Split'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['London'],
        days[i] == city_indices['Porto'],
    ))

# Define direct flight connections
direct_flights = [
    (2, 1),  # London to Oslo
    (0, 1),  # Split to Oslo
    (1, 3),  # Oslo to Porto
    (2, 0),  # London to Split
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
        print(f"Day {i + 1}: City code {city_code} (0=Split, 1=Oslo, 2=London, 3=Porto)")
else:
    print("No solution found.")