from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 12

# Define the days spent in each city
cities = {
    'Riga': Int('days_in_riga'),      # 5 days
    'Vilnius': Int('days_in_vilnius'), # 7 days
    'Dublin': Int('days_in_dublin'),   # 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Riga'] == 5)
solver.add(cities['Vilnius'] == 7)
solver.add(cities['Dublin'] == 2)

# Total days must sum to 12
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 12 days (0-2 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Ensure daily assignments only use valid city indices
city_indices = {
    'Riga': 0,
    'Vilnius': 1,
    'Dublin': 2,
}

for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Dublin'],
    ))

# Define direct flight connections
direct_flights = [
    (2, 0),  # Dublin to Riga
    (0, 1),  # Riga to Vilnius
]

# Ensure that flights match the travel plan
for i in range(total_days - 1):
    for src, dst in direct_flights:
        solver.add(If(days[i] == src, days[i + 1] == dst, True))

# Solve the scheduling problem
if solver.check() == sat:
    model = solver.model()
    print("Schedule:")
    for i in range(total_days):
        city_code = model[days[i]].as_long()
        print(f"Day {i + 1}: City code {city_code} (0=Riga, 1=Vilnius, 2=Dublin)")
else:
    print("No solution found.")