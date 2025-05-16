from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 23

# Define the days spent in each city
cities = {
    'Paris': Int('days_in_paris'),      # 6 days
    'Oslo': Int('days_in_oslo'),        # 5 days
    'Porto': Int('days_in_porto'),      # 7 days
    'Geneva': Int('days_in_geneva'),    # 7 days
    'Reykjavik': Int('days_in_reykjavik')  # 2 days
}

# Add constraints for days spent in each city
solver.add(cities['Paris'] == 6)
solver.add(cities['Oslo'] == 5)
solver.add(cities['Porto'] == 7)
solver.add(cities['Geneva'] == 7)
solver.add(cities['Reykjavik'] == 2)

# Total days must sum to 23
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 23 days (0-4 for each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a conference in Geneva (on day 1 and day 7)
solver.add(days[0] == 3)  # Geneva (index 3) on day 1
solver.add(days[6] == 3)  # Geneva (index 3) on day 7

# Visit relatives in Oslo (between day 19 and day 23)
for i in range(18, 23):  # Days 19 to 23
    solver.add(days[i] == 1)  # Oslo (index 1)

# Define valid city indices
city_indices = {
    'Paris': 0,
    'Oslo': 1,
    'Porto': 2,
    'Geneva': 3,
    'Reykjavik': 4,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Porto'],
        days[i] == city_indices['Geneva'],
        days[i] == city_indices['Reykjavik'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 1),  # Paris to Oslo
    (1, 3),  # Oslo to Geneva
    (2, 0),  # Porto to Paris
    (3, 0),  # Geneva to Paris
    (2, 3),  # Porto to Geneva
    (0, 4),  # Paris to Reykjavik
    (4, 1),  # Reykjavik to Oslo
    (2, 1),  # Porto to Oslo
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
        print(f"Day {i + 1}: City code {city_code} (0=Paris, 1=Oslo, 2=Porto, 3=Geneva, 4=Reykjavik)")
else:
    print("No solution found.")