from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Total days of the trip
total_days = 16

# Define the days spent in each city
cities = {
    'Mykonos': Int('days_in_mykonos'),      # 4 days
    'Nice': Int('days_in_nice'),            # 3 days
    'London': Int('days_in_london'),        # 2 days
    'Copenhagen': Int('days_in_copenhagen'),# 3 days
    'Oslo': Int('days_in_oslo'),            # 5 days
    'Tallinn': Int('days_in_tallinn'),      # 4 days
}

# Add constraints on days spent in each city
solver.add(cities['Mykonos'] == 4)
solver.add(cities['Nice'] == 3)
solver.add(cities['London'] == 2)
solver.add(cities['Copenhagen'] == 3)
solver.add(cities['Oslo'] == 5)
solver.add(cities['Tallinn'] == 4)

# Total days must sum to 16
solver.add(Sum([cities[city] for city in cities]) == total_days)

# Daily assignments for 16 days (0-5 representing each city)
days = [Int(f'day_{i}') for i in range(total_days)]

# Constraints for specific events
# Attend a conference in Nice (on day 14 and day 16)
solver.add(days[13] == 1)  # Nice (index 1) on day 14
solver.add(days[15] == 1)  # Nice (index 1) on day 16

# Meet a friend in Oslo (between day 10 and day 14)
# This means day 10, day 11, day 12, and day 13 must include Oslo
for i in range(9, 14):
    solver.add(days[i] == 4)  # Oslo (index 4)

# Define valid city indices
city_indices = {
    'Mykonos': 0,
    'Nice': 1,
    'London': 2,
    'Copenhagen': 3,
    'Oslo': 4,
    'Tallinn': 5,
}

# Ensure daily assignments only use valid city indices
for i in range(total_days):
    solver.add(Or(
        days[i] == city_indices['Mykonos'],
        days[i] == city_indices['Nice'],
        days[i] == city_indices['London'],
        days[i] == city_indices['Copenhagen'],
        days[i] == city_indices['Oslo'],
        days[i] == city_indices['Tallinn'],
    ))

# Define direct flight connections
direct_flights = [
    (2, 3),  # London to Copenhagen
    (3, 5),  # Copenhagen to Tallinn
    (5, 4),  # Tallinn to Oslo
    (0, 2),  # Mykonos to London
    (4, 1),  # Oslo to Nice
    (2, 1),  # London to Nice
    (0, 1),  # Mykonos to Nice
    (2, 4),  # London to Oslo
    (3, 1),  # Copenhagen to Nice
    (3, 4),  # Copenhagen to Oslo
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
        print(f"Day {i + 1}: City code {city_code} (0=Mykonos, 1=Nice, 2=London, 3=Copenhagen, 4=Oslo, 5=Tallinn)")
else:
    print("No solution found.")