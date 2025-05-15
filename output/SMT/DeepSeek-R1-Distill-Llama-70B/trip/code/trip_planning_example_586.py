from z3 import *

# Define the cities
cities = ["Frankfurt", "Naples", "Helsinki", "Lyon", "Prague"]

# Required days for each city
required_days = {
    "Frankfurt": 3,
    "Naples": 4,
    "Helsinki": 4,
    "Lyon": 3,
    "Prague": 2
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(12)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("Prague", "Lyon"), ("Prague", "Frankfurt"),
    ("Frankfurt", "Lyon"), ("Helsinki", "Naples"),
    ("Helsinki", "Frankfurt"), ("Naples", "Frankfurt"),
    ("Prague", "Helsinki")
}

# Add constraints for fixed time windows
solver.add(Or([days[0] == "Prague", days[1] == "Prague"]))  # Prague on day 1 or 2

for i in range(1, 5):  # days 2-5 (indices 1 to 4)
    solver.add(days[i] == "Helsinki")

# For each consecutive day pair, add flight constraint
for i in range(11):
    a = days[i]
    b = days[i+1]
    solver.add(Or([And(a == c1, b == c2) for (c1, c2) in direct_flights]))

# Add constraints for the number of days in each city
# We need to count both the days assigned and the days arrived via flights
for city in cities:
    count_days_assigned = 0
    count_flights_arrived = 0
    for i in range(12):
        count_days_assigned += If(days[i] == city, 1, 0)
    for i in range(11):
        count_flights_arrived += If(days[i+1] == city, 1, 0)
    total = count_days_assigned + count_flights_arrived
    solver.add(total == required_days[city])

# Solve the problem
result = solver.check()
if result == sat:
    model = solver.model()
    for i in range(12):
        print(f"Day {i+1}: {model[days[i]]}")
else:
    print("No solution exists")