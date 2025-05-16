from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 7

# Define the days spent in each city
cities = {
    'Madrid': Int('days_in_madrid'),  # 4 days
    'Dublin': Int('days_in_dublin'),  # 3 days
    'Tallinn': Int('days_in_tallinn'),# 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Madrid'] == 4)
solver.add(cities['Dublin'] == 3)
solver.add(cities['Tallinn'] == 2)

# Total days must sum to 7
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 7 days (0-2 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a workshop in Tallinn (on day 6 and day 7)
solver.add(days[5] == 2)  # Tallinn (index 2) on day 6
solver.add(days[6] == 2)  # Tallinn (index 2) on day 7

# Define valid city indices
city_indices = {
    'Madrid': 0,
    'Dublin': 1,
    'Tallinn': 2,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Madrid'],
        days[i] == city_indices['Dublin'],
        days[i] == city_indices['Tallinn'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 1),  # Madrid to Dublin
    (1, 2),  # Dublin to Tallinn
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
        print(f"Day {i + 1}: City code {city_code} (0=Madrid, 1=Dublin, 2=Tallinn)")
else:
    print("No solution found.")