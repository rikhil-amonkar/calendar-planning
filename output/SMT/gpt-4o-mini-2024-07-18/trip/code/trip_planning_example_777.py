from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 15

# Define the days spent in each city
cities = {
    'Dublin': Int('days_in_dublin'),      # 5 days
    'Helsinki': Int('days_in_helsinki'),  # 3 days
    'Riga': Int('days_in_riga'),          # 3 days
    'Reykjavik': Int('days_in_reykjavik'),# 2 days
    'Vienna': Int('days_in_vienna'),      # 2 days
    'Tallinn': Int('days_in_tallinn'),    # 5 days
}

# Add constraints on days spent in each city
solver.add(cities['Dublin'] == 5)
solver.add(cities['Helsinki'] == 3)
solver.add(cities['Riga'] == 3)
solver.add(cities['Reykjavik'] == 2)
solver.add(cities['Vienna'] == 2)
solver.add(cities['Tallinn'] == 5)

# Total days must sum to 15
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 15 days (0-5 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meet friends in Helsinki (between day 3 and day 5)
solver.add(days[2] == 1)  # Helsinki (index 1) on day 3
solver.add(days[3] == 1)  # Helsinki (index 1) on day 4

# Attend an annual show in Vienna (on day 2 and day 3)
solver.add(days[1] == 4)  # Vienna (index 4) on day 2
solver.add(days[2] == 4)  # Vienna (index 4) on day 3

# Attend a wedding in Tallinn (between day 7 and day 11)
for i in range(6, 11):  # Days 7 to 11
    solver.add(days[i] == 5)  # Tallinn (index 5)

# Define valid city indices
city_indices = {
    'Dublin': 0,
    'Helsinki': 1,
    'Riga': 2,
    'Reykjavik': 3,
    'Vienna': 4,
    'Tallinn': 5,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Dublin'],
        days[i] == city_indices['Helsinki'],
        days[i] == city_indices['Riga'],
        days[i] == city_indices['Reykjavik'],
        days[i] == city_indices['Vienna'],
        days[i] == city_indices['Tallinn'],
    ))

# Define direct flight connections
direct_flights = [
    (1, 2),  # Helsinki to Riga
    (2, 5),  # Riga to Tallinn
    (4, 1),  # Vienna to Helsinki
    (2, 0),  # Riga to Dublin
    (4, 2),  # Vienna to Riga
    (3, 4),  # Reykjavik to Vienna
    (1, 0),  # Helsinki to Dublin
    (5, 0),  # Tallinn to Dublin
    (3, 1),  # Reykjavik to Helsinki
    (3, 0),  # Reykjavik to Dublin
    (1, 5),  # Helsinki to Tallinn
    (4, 0),  # Vienna to Dublin
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
        print(f"Day {i + 1}: City code {city_code} (0=Dublin, 1=Helsinki, 2=Riga, 3=Reykjavik, 4=Vienna, 5=Tallinn)")
else:
    print("No solution found.")