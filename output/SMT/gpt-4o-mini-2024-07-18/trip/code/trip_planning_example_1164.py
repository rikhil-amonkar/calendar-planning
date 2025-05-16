from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 17

# Define the days spent in each city
cities = {
    'Reykjavik': Int('days_in_reykjavik'),  # 2 days
    'Stockholm': Int('days_in_stockholm'),  # 2 days
    'Porto': Int('days_in_porto'),          # 5 days
    'Nice': Int('days_in_nice'),            # 3 days
    'Venice': Int('days_in_venice'),        # 4 days
    'Vienna': Int('days_in_vienna'),        # 3 days
    'Split': Int('days_in_split'),          # 3 days
    'Copenhagen': Int('days_in_copenhagen'),# 2 days
}

# Add constraints on days spent in each city
solver.add(cities['Reykjavik'] == 2)
solver.add(cities['Stockholm'] == 2)
solver.add(cities['Porto'] == 5)
solver.add(cities['Nice'] == 3)
solver.add(cities['Venice'] == 4)
solver.add(cities['Vienna'] == 3)
solver.add(cities['Split'] == 3)
solver.add(cities['Copenhagen'] == 2)

# Total days must sum to 17
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily city assignments for 17 days (0-7 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Meet a friend in Reykjavik (between day 3 and day 4)
solver.add(days[2] == 0)  # Reykjavik (index 0) on day 3
solver.add(days[3] == 0)  # Reykjavik (index 0) on day 4

# Meet friends in Stockholm (between day 4 and day 5)
solver.add(days[3] == 1)  # Stockholm (index 1) on day 4
solver.add(days[4] == 1)  # Stockholm (index 1) on day 5

# Attend a wedding in Porto (between day 13 and day 17)
for i in range(12, total_days):  # Days 13 to 17
    solver.add(days[i] == 2)  # Porto (index 2)

# Attend a workshop in Vienna (between day 11 and day 13)
for i in range(10, 12):  # Days 11 to 12
    solver.add(days[i] == 5)  # Vienna (index 5)

# Define valid city indices
city_indices = {
    'Reykjavik': 0,
    'Stockholm': 1,
    'Porto': 2,
    'Nice': 3,
    'Venice': 4,
    'Vienna': 5,
    'Split': 6,
    'Copenhagen': 7,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Reykjavik'],
        days[i] == city_indices['Stockholm'],
        days[i] == city_indices['Porto'],
        days[i] == city_indices['Nice'],
        days[i] == city_indices['Venice'],
        days[i] == city_indices['Vienna'],
        days[i] == city_indices['Split'],
        days[i] == city_indices['Copenhagen'],
    ))

# Define direct flight connections
direct_flights = [
    (7, 5),  # Copenhagen to Vienna
    (3, 1),  # Nice to Stockholm
    (6, 7),  # Split to Copenhagen
    (3, 0),  # Nice to Reykjavik
    (3, 2),  # Nice to Porto
    (4, 0),  # Venice to Reykjavik
    (4, 6),  # Venice to Split
    (0, 5),  # Reykjavik to Vienna
    (1, 7),  # Stockholm to Copenhagen
    (0, 1),  # Reykjavik to Stockholm
    (1, 4),  # Stockholm to Venice
    (1, 2),  # Stockholm to Porto
    (3, 4),  # Nice to Venice
    (5, 2),  # Vienna to Porto
    (4, 2),  # Venice to Porto
    (5, 7),  # Vienna to Copenhagen
    (7, 2),  # Copenhagen to Porto
    (6, 5),  # Split to Vienna
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
        print(f"Day {i + 1}: City code {city_code} (0=Reykjavik, 1=Stockholm, 2=Porto, 3=Nice, 4=Venice, 5=Vienna, 6=Split, 7=Copenhagen)")
else:
    print("No solution found.")