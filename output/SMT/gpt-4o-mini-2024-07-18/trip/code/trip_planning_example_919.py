from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 15

# Define the days spent in each city
cities = {
    'Vienna': Int('days_in_vienna'),      # 4 days
    'Milan': Int('days_in_milan'),        # 2 days
    'Rome': Int('days_in_rome'),          # 3 days
    'Riga': Int('days_in_riga'),          # 2 days
    'Lisbon': Int('days_in_lisbon'),      # 3 days
    'Vilnius': Int('days_in_vilnius'),    # 4 days
    'Oslo': Int('days_in_oslo'),          # 3 days
}

# Add constraints on days spent in each city
solver.add(cities['Vienna'] == 4)
solver.add(cities['Milan'] == 2)
solver.add(cities['Rome'] == 3)
solver.add(cities['Riga'] == 2)
solver.add(cities['Lisbon'] == 3)
solver.add(cities['Vilnius'] == 4)
solver.add(cities['Oslo'] == 3)

# Total days must sum to 15
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 15 days (0-6 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Conference in Vienna on day 1 and day 4
solver.add(days[0] == 0)  # Vienna (index 0) on day 1
solver.add(days[3] == 0)  # Vienna (index 0) on day 4

# Visit relatives in Lisbon (between day 11 and 13)
solver.add(days[10] == 4)  # Lisbon (index 4) on day 11
solver.add(days[11] == 4)  # Lisbon (index 4) on day 12
solver.add(days[12] == 4)  # Lisbon (index 4) on day 13

# Meet a friend in Oslo (between day 13 and 15)
solver.add(days[12] == 5)  # Oslo (index 5) on day 13
solver.add(days[13] == 5)  # Oslo (index 5) on day 14

# Define valid city indices
city_indices = {
    'Vienna': 0,
    'Milan': 1,
    'Rome': 2,
    'Riga': 3,
    'Lisbon': 4,
    'Vilnius': 5,
    'Oslo': 6,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Vienna'],
        days[i] == city_indices['Milan'],
        days[i] == city_indices['Rome'],
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Lisbon'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Oslo'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 1),  # Vienna to Milan
    (0, 5),  # Vienna to Vilnius
    (0, 4),  # Vienna to Lisbon
    (1, 6),  # Milan to Oslo
    (2, 6),  # Rome to Oslo
    (2, 3),  # Rome to Riga
    (2, 4),  # Rome to Lisbon
    (3, 5),  # Riga to Vilnius
    (3, 4),  # Riga to Lisbon
    (4, 6),  # Lisbon to Oslo
    (5, 6),  # Vilnius to Oslo
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
        print(f"Day {i + 1}: City code {city_code} (0=Vienna, 1=Milan, 2=Rome, 3=Riga, 4=Lisbon, 5=Vilnius, 6=Oslo)")
else:
    print("No solution found.")