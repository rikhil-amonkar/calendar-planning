from z3 import *

# Define the cities
cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]

# Required days for each city
required_days = {
    "Tallinn": 2,
    "Bucharest": 4,
    "Seville": 5,
    "Stockholm": 5,
    "Munich": 5,
    "Milan": 2
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(18)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("Milan", "Stockholm"), ("Munich", "Stockholm"),
    ("Bucharest", "Munich"), ("Munich", "Seville"),
    ("Stockholm", "Tallinn"), ("Munich", "Milan"),
    ("Munich", "Tallinn"), ("Seville", "Milan")
}

# Add constraints for fixed time windows
for i in range(4):  # days 1-4 (indices 0 to 3)
    solver.add(days[i] == "Bucharest")

for i in range(3, 8):  # days 4-8 (indices 3 to 7)
    solver.add(days[i] == "Munich")

for i in range(7, 12):  # days 8-12 (indices 7 to 11)
    solver.add(days[i] == "Seville")

# For each consecutive day pair, add flight constraint
for i in range(17):
    a = days[i]
    b = days[i+1]
    solver.add(Or([And(a == c1, b == c2) for (c1, c2) in direct_flights]))

# Add constraints for the number of days in each city
# We need to count both the days assigned and the days arrived via flights
for city in cities:
    count_days_assigned = 0
    count_flights_arrived = 0
    for i in range(18):
        count_days_assigned += If(days[i] == city, 1, 0)
    for i in range(17):
        count_flights_arrived += If(days[i+1] == city, 1, 0)
    total = count_days_assigned + count_flights_arrived
    solver.add(total == required_days[city])

# Solve the problem
result = solver.check()
if result == sat:
    model = solver.model()
    for i in range(18):
        print(f"Day {i+1}: {model[days[i]]}")
else:
    print("No solution exists")