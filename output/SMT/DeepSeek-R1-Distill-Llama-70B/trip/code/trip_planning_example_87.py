from z3 import *

# Define the cities
cities = ["Riga", "Amsterdam", "Mykonos"]

# Required days for each city
required_days = {
    "Riga": 2,
    "Amsterdam": 2,
    "Mykonos": 5
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(7)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("Amsterdam", "Mykonos"),
    ("Riga", "Amsterdam")
}

# Add constraints for fixed time windows
solver.add(Or([days[0] == "Riga", days[1] == "Riga"]))  # Riga on day 1 or 2

# For each consecutive day pair, add flight constraint
for i in range(6):
    a = days[i]
    b = days[i+1]
    solver.add(Or([And(a == c1, b == c2) for (c1, c2) in direct_flights]))

# Add constraints for the number of days in each city
# We need to count both the days assigned and the days arrived via flights
for city in cities:
    count_days_assigned = 0
    count_flights_arrived = 0
    for i in range(7):
        count_days_assigned += If(days[i] == city, 1, 0)
    for i in range(6):
        count_flights_arrived += If(days[i+1] == city, 1, 0)
    total = count_days_assigned + count_flights_arrived
    solver.add(total == required_days[city])

# Solve the problem
result = solver.check()
if result == sat:
    model = solver.model()
    for i in range(7):
        print(f"Day {i+1}: {model[days[i]]}")
else:
    print("No solution exists")