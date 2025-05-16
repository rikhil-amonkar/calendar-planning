from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 20

# Define the days spent in each city
cities = {
    'Paris': Int('days_in_paris'),        # 5 days
    'Florence': Int('days_in_florence'),  # 3 days
    'Vienna': Int('days_in_vienna'),      # 2 days
    'Porto': Int('days_in_porto'),        # 3 days
    'Munich': Int('days_in_munich'),      # 5 days
    'Nice': Int('days_in_nice'),          # 5 days
    'Warsaw': Int('days_in_warsaw'),      # 3 days
}

# Add constraints on days spent in each city
solver.add(cities['Paris'] == 5)
solver.add(cities['Florence'] == 3)
solver.add(cities['Vienna'] == 2)
solver.add(cities['Porto'] == 3)
solver.add(cities['Munich'] == 5)
solver.add(cities['Nice'] == 5)
solver.add(cities['Warsaw'] == 3)

# Total days must sum to 20
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 20 days (0-6 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a workshop in Porto (day 1 to 3)
solver.add(days[0] == 3)  # Porto (index 3) on day 1
solver.add(days[1] == 3)  # Porto (index 3) on day 2
solver.add(days[2] == 3)  # Porto (index 3) on day 3

# Visit relatives in Vienna (day 19 to 20)
solver.add(days[18] == 2)  # Vienna (index 2) on day 19
solver.add(days[19] == 2)  # Vienna (index 2) on day 20

# Attend a wedding in Warsaw (day 13 to 15)
solver.add(days[12] == 6)  # Warsaw (index 6) on day 13
solver.add(days[13] == 6)  # Warsaw (index 6) on day 14
solver.add(days[14] == 6)  # Warsaw (index 6) on day 15

# Define valid city indices
city_indices = {
    'Paris': 0,
    'Florence': 1,
    'Vienna': 2,
    'Porto': 3,
    'Munich': 4,
    'Nice': 5,
    'Warsaw': 6,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Paris'],
        days[i] == city_indices['Florence'],
        days[i] == city_indices['Vienna'],
        days[i] == city_indices['Porto'],
        days[i] == city_indices['Munich'],
        days[i] == city_indices['Nice'],
        days[i] == city_indices['Warsaw'],
    ))

# Define direct flight connections
direct_flights = [
    (1, 2),  # Florence to Vienna
    (0, 6),  # Paris to Warsaw
    (4, 2),  # Munich to Vienna
    (3, 2),  # Porto to Vienna
    (6, 2),  # Warsaw to Vienna
    (1, 4),  # Florence to Munich
    (4, 6),  # Munich to Warsaw
    (4, 5),  # Munich to Nice
    (0, 1),  # Paris to Florence
    (6, 5),  # Warsaw to Nice
    (3, 1),  # Porto to Florence
    (3, 4),  # Porto to Munich
    (4, 0),  # Munich to Paris
    (5, 2),  # Nice to Vienna
    (4, 5),  # Munich to Nice
    (3, 0),  # Porto to Paris
    (0, 5),  # Paris to Nice
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
        print(f"Day {i + 1}: City code {city_code} (0=Paris, 1=Florence, 2=Vienna, 3=Porto, 4=Munich, 5=Nice, 6=Warsaw)")
else:
    print("No solution found.")