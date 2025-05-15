from z3 import *

# Define the cities
cities = ["Nice", "Stockholm", "Split", "Vienna"]

# Required days for each city
required_days = {
    "Nice": 2,
    "Stockholm": 5,
    "Split": 3,
    "Vienna": 2
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(9)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("Vienna", "Stockholm"), ("Vienna", "Nice"),
    ("Vienna", "Split"), ("Stockholm", "Split"),
    ("Nice", "Stockholm")
}

# Add constraints for fixed time windows
solver.add(Or([days[0] == "Vienna", days[1] == "Vienna"]))  # Vienna on day 1 or 2

solver.add(Or([days[6] == "Split", days[7] == "Split", days[8] == "Split"]))  # Split on day 7, 8, or 9

# For each consecutive day pair, add flight constraint
for i in range(8):
    a = days[i]
    b = days[i+1]
    solver.add(Or([And(a == c1, b == c2) for (c1, c2) in direct_flights]))

# Add constraints for the number of days in each city
# We need to count both the days assigned and the days arrived via flights
for city in cities:
    count_days_assigned = 0
    count_flights_arrived = 0
    for i in range(9):
        count_days_assigned += If(days[i] == city, 1, 0)
    for i in range(8):
        count_flights_arrived += If(days[i+1] == city, 1, 0)
    total = count_days_assigned + count_flights_arrived
    solver.add(total == required_days[city])

# Solve the problem
result = solver.check()
if result == sat:
    model = solver.model()
    for i in range(9):
        print(f"Day {i+1}: {model[days[i]]}")
else:
    print("No solution exists")