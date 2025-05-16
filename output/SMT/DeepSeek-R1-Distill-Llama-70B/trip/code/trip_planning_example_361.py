from z3 import *

# Define the cities
cities = ["Paris", "Madrid", "Bucharest", "Seville"]

# Required days for each city
required_days = {
    "Paris": 6,
    "Madrid": 7,
    "Bucharest": 2,
    "Seville": 3
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(15)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("Paris", "Bucharest"), ("Seville", "Paris"),
    ("Madrid", "Bucharest"), ("Madrid", "Paris"),
    ("Madrid", "Seville")
}

# Add constraints for fixed time windows
for i in range(7):  # days 1-7 (indices 0 to 6)
    solver.add(days[i] == "Madrid")

solver.add(days[13] == "Bucharest")  # day 14
solver.add(days[14] == "Bucharest")  # day 15

# For each consecutive day pair, add flight constraint
for i in range(14):
    a = days[i]
    b = days[i+1]
    solver.add(Or([And(a == c1, b == c2) for (c1, c2) in direct_flights]))

# Add constraints for the number of days in each city
# We need to count both the days assigned and the days arrived via flights
for city in cities:
    count_days_assigned = 0
    count_flights_arrived = 0
    for i in range(15):
        count_days_assigned += If(days[i] == city, 1, 0)
    for i in range(14):
        count_flights_arrived += If(days[i+1] == city, 1, 0)
    total = count_days_assigned + count_flights_arrived
    solver.add(total == required_days[city])

# Solve the problem
result = solver.check()
if result == sat:
    model = solver.model()
    for i in range(15):
        print(f"Day {i+1}: {model[days[i]]}")
else:
    print("No solution exists")