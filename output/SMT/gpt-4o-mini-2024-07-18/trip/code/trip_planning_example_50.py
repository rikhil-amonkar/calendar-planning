from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 12

# Define the days spent in each city
cities = {
    'Vilnius': Int('days_in_vilnius'),  # 4 days
    'Munich': Int('days_in_munich'),    # 3 days
    'Mykonos': Int('days_in_mykonos'),  # 7 days
}

# Add constraints on days spent in each city
solver.add(cities['Vilnius'] == 4)
solver.add(cities['Munich'] == 3)
solver.add(cities['Mykonos'] == 7)

# Total days must sum to 12
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 12 days (0-2 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Ensure daily assignments use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == 0,  # Vilnius
        days[i] == 1,  # Munich
        days[i] == 2   # Mykonos
    ))

# Define valid city indices
city_indices = {
    'Vilnius': 0,
    'Munich': 1,
    'Mykonos': 2,
}

# Add direct flight constraints
direct_flights = [
    (0, 1),  # Vilnius to Munich
    (1, 2),  # Munich to Mykonos
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
        print(f"Day {i + 1}: City code {city_code} (0=Vilnius, 1=Munich, 2=Mykonos)")
else:
    print("No solution found.")