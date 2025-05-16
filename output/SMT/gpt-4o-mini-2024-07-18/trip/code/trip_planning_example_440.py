from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 12

# Define the days spent in each city
cities = {
    'Split': Int('days_in_split'),        # 2 days
    'Helsinki': Int('days_in_helsinki'),  # 2 days
    'Reykjavik': Int('days_in_reykjavik'),# 3 days
    'Vilnius': Int('days_in_vilnius'),    # 3 days
    'Geneva': Int('days_in_geneva'),      # 6 days
}

# Add constraints on days spent in each city
solver.add(cities['Split'] == 2)
solver.add(cities['Helsinki'] == 2)
solver.add(cities['Reykjavik'] == 3)
solver.add(cities['Vilnius'] == 3)
solver.add(cities['Geneva'] == 6)

# Total days must sum to 12
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 12 days (0-4 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a wedding in Reykjavik (between day 10 to 12)
solver.add(days[9] == 2)  # Reykjavik (index 2) on day 10
solver.add(days[10] == 2)  # Reykjavik (index 2) on day 11
solver.add(days[11] == 2)  # Reykjavik (index 2) on day 12

# Visit relatives in Vilnius (between day 7 to 9)
solver.add(days[6] == 3)  # Vilnius (index 3) on day 7
solver.add(days[7] == 3)  # Vilnius (index 3) on day 8

# Define valid city indices
city_indices = {
    'Split': 0,
    'Helsinki': 1,
    'Reykjavik': 2,
    'Vilnius': 3,
    'Geneva': 4,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Split'],
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Reykjavik'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Geneva'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 1),  # Split to Helsinki
    (4, 0),  # Geneva to Split
    (4, 1),  # Geneva to Helsinki
    (1, 2),  # Helsinki to Reykjavik
    (3, 1),  # Vilnius to Helsinki
    (0, 3),  # Split to Vilnius
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
        print(f"Day {i + 1}: City code {city_code} (0=Split, 1=Helsinki, 2=Reykjavik, 3=Vilnius, 4=Geneva)")
else:
    print("No solution found.")