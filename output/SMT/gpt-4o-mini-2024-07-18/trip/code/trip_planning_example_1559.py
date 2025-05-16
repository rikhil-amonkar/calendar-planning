from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 25

# Define the days spent in each city
cities = {
    'Valencia': Int('days_in_valencia'),    # 2 days
    'Oslo': Int('days_in_oslo'),            # 3 days
    'Lyon': Int('days_in_lyon'),            # 4 days
    'Prague': Int('days_in_prague'),        # 3 days
    'Paris': Int('days_in_paris'),          # 4 days
    'Nice': Int('days_in_nice'),            # 4 days
    'Seville': Int('days_in_seville'),      # 5 days
    'Tallinn': Int('days_in_tallinn'),      # 2 days
    'Mykonos': Int('days_in_mykonos'),      # 5 days
    'Lisbon': Int('days_in_lisbon'),        # 2 days
}

# Add constraints on the number of days spent in each city
solver.add(cities['Valencia'] == 2)
solver.add(cities['Oslo'] == 3)
solver.add(cities['Lyon'] == 4)
solver.add(cities['Prague'] == 3)
solver.add(cities['Paris'] == 4)
solver.add(cities['Nice'] == 4)
solver.add(cities['Seville'] == 5)
solver.add(cities['Tallinn'] == 2)
solver.add(cities['Mykonos'] == 5)
solver.add(cities['Lisbon'] == 2)

# Total days must sum to 25
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 25 days (0-9 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meeting friends in Valencia (between day 3 and day 4)
solver.add(days[2] == 0)  # Valencia on day 3
solver.add(days[3] == 0)  # Valencia on day 4

# Meeting a friend in Oslo (between day 13 and day 15)
solver.add(days[12] == 1)  # Oslo on day 13
solver.add(days[13] == 1)  # Oslo on day 14
solver.add(days[14] == 1)  # Oslo on day 15

# Annual show in Seville (between day 5 and day 9)
for i in range(4, 9):  # Days 5 to 9
    solver.add(days[i] == 6)  # Seville

# Wedding in Mykonos (between day 21 and day 25)
for i in range(20, 25):  # Days 21 to 25
    solver.add(days[i] == 8)  # Mykonos

# Define valid city indices
city_indices = {
    'Valencia': 0,
    'Oslo': 1,
    'Lyon': 2,
    'Prague': 3,
    'Paris': 4,
    'Nice': 5,
    'Seville': 6,
    'Tallinn': 7,
    'Mykonos': 8,
    'Lisbon': 9,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Valencia'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Lyon'],
        days[i] == city_indices['Prague'],
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Nice'],
        days[i] == city_indices['Seville'],
        days[i] == city_indices['Tallinn'],
        days[i] == city_indices['Mykonos'],
        days[i] == city_indices['Lisbon'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 4),  # Valencia to Paris
    (1, 2),  # Oslo to Lyon
    (1, 4),  # Oslo to Paris
    (2, 5),  # Lyon to Nice
    (3, 2),  # Prague to Lyon
    (4, 5),  # Paris to Nice
    (4, 1),  # Paris to Oslo
    (4, 3),  # Paris to Prague
    (4, 9),  # Paris to Lisbon
    (6, 4),  # Seville to Paris
    (7, 1),  # Tallinn to Oslo
    (9, 4),  # Lisbon to Paris
    (9, 0),  # Lisbon to Valencia
    (0, 6),  # Valencia to Seville
    (9, 6),  # Lisbon to Seville
    (2, 0),  # Lyon to Valencia
    (9, 2),  # Lisbon to Lyon
    (8, 3),  # Mykonos to Prague
    (3, 7),  # Prague to Tallinn
    (5, 8),  # Nice to Mykonos
    (5, 9),  # Nice to Lisbon
    (3, 1),  # Prague to Oslo
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
        print(f"Day {i + 1}: City code {city_code} (0=Valencia, 1=Oslo, 2=Lyon, 3=Prague, 4=Paris, 5=Nice, 6=Seville, 7=Tallinn, 8=Mykonos, 9=Lisbon)")
else:
    print("No solution found.")