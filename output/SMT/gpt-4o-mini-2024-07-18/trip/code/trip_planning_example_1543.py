from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 26

# Define the days spent in each city
cities = {
    'Prague': Int('days_in_prague'),       # 3 days
    'Warsaw': Int('days_in_warsaw'),       # 4 days
    'Dublin': Int('days_in_dublin'),       # 3 days
    'Athens': Int('days_in_athens'),       # 3 days
    'Vilnius': Int('days_in_vilnius'),     # 4 days
    'Porto': Int('days_in_porto'),         # 5 days
    'London': Int('days_in_london'),       # 3 days
    'Seville': Int('days_in_seville'),     # 2 days
    'Lisbon': Int('days_in_lisbon'),       # 5 days
    'Dubrovnik': Int('days_in_dubrovnik'), # 3 days
}

# Add constraints on days spent in each city
solver.add(cities['Prague'] == 3)
solver.add(cities['Warsaw'] == 4)
solver.add(cities['Dublin'] == 3)
solver.add(cities['Athens'] == 3)
solver.add(cities['Vilnius'] == 4)
solver.add(cities['Porto'] == 5)
solver.add(cities['London'] == 3)
solver.add(cities['Seville'] == 2)
solver.add(cities['Lisbon'] == 5)
solver.add(cities['Dubrovnik'] == 3)

# Total days must sum to 26
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 26 days (0-9 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a workshop in Prague (between day 1 and day 3)
solver.add(days[0] == 0)  # Prague (index 0) on day 1
solver.add(days[1] == 0)  # Prague (index 0) on day 2
solver.add(days[2] == 0)  # Prague (index 0) on day 3

# Attend a conference in Porto (on day 16 and day 20)
solver.add(days[15] == 5)  # Porto (index 5) on day 16
solver.add(days[19] == 5)  # Porto (index 5) on day 20

# Attend a wedding in London (between day 3 and day 5)
solver.add(days[3] == 7)  # London (index 7) on day 4
solver.add(days[4] == 7)  # London (index 7) on day 5

# Meet friends in Warsaw (between day 20 and day 23)
solver.add(days[19] == 1)  # Warsaw (index 1) on day 20
solver.add(days[20] == 1)  # Warsaw (index 1) on day 21
solver.add(days[21] == 1)  # Warsaw (index 1) on day 22

# Define valid city indices
city_indices = {
    'Prague': 0,
    'Warsaw': 1,
    'Dublin': 2,
    'Athens': 3,
    'Vilnius': 4,
    'Porto': 5,
    'London': 6,
    'Seville': 7,
    'Lisbon': 8,
    'Dubrovnik': 9,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Prague'],
        days[i] == city_indices['Warsaw'],
        days[i] == city_indices['Dublin'],
        days[i] == city_indices['Athens'],
        days[i] == city_indices['Vilnius'],
        days[i] == city_indices['Porto'],
        days[i] == city_indices['London'],
        days[i] == city_indices['Seville'],
        days[i] == city_indices['Lisbon'],
        days[i] == city_indices['Dubrovnik'],
    ))

# Define direct flight connections
direct_flights = [
    (0, 3),  # Prague to Athens
    (1, 4),  # Warsaw to Vilnius
    (5, 2),  # Dublin to Seville
    (7, 5),  # Seville to Porto
    (7, 8),  # Seville to Lisbon
    (6, 8),  # London to Lisbon
    (6, 2),  # London to Dublin
    (3, 2),  # Athens to Dublin
    (3, 4),  # Athens to Vilnius
    (2, 5),  # Dublin to Porto
    (2, 4),  # Dublin to Vilnius
    (4, 5),  # Vilnius to Porto
    (8, 5),  # Lisbon to Porto
    (1, 6),  # Warsaw to London
    (4, 6),  # Vilnius to London
    (3, 6),  # Athens to London
    (9, 2)   # Dubrovnik to Dublin
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
        print(f"Day {i + 1}: City code {city_code} (0=Prague, 1=Warsaw, 2=Dublin, 3=Athens, 4=Vilnius, 5=Porto, 6=London, 7=Seville, 8=Lisbon, 9=Dubrovnik)")
else:
    print("No solution found.")