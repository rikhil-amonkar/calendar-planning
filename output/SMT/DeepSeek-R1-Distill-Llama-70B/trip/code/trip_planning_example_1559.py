from z3 import *

# Define the cities
cities = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]

# Required days for each city
required_days = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(25)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"),
    ("Prague", "Lyon"), ("Paris", "Oslo"), ("Lisbon", "Seville"),
    ("Prague", "Lisbon"), ("Oslo", "Nice"), ("Valencia", "Paris"),
    ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
    ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"),
    ("Prague", "Paris"), ("Seville", "Paris"), ("Oslo", "Lyon"),
    ("Prague", "Valencia"), ("Lisbon", "Nice"), ("Lisbon", "Oslo"),
    ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
}

# Add constraints for fixed time windows
solver.add(Or([days[2] == "Valencia", days[3] == "Valencia"]))  # Valencia on day 3 or 4

solver.add(Or([days[i] == "Oslo" for i in range(12, 15)]))  # Oslo between day 13-15

solver.add(Or([days[i] == "Seville" for i in range(4, 10)]))  # Seville between day 5-9

solver.add(Or([days[i] == "Mykonos" for i in range(20, 25)]))  # Mykonos between day 21-25

# For each consecutive day pair, add flight constraint
for i in range(24):
    a = days[i]
    b = days[i+1]
    solver.add(Or([And(a == c1, b == c2) for (c1, c2) in direct_flights]))

# Add constraints for the number of days in each city
# We need to count both the days assigned and the days arrived via flights
for city in cities:
    count_days_assigned = 0
    count_flights_arrived = 0
    for i in range(25):
        count_days_assigned += If(days[i] == city, 1, 0)
    for i in range(24):
        count_flights_arrived += If(days[i+1] == city, 1, 0)
    total = count_days_assigned + count_flights_arrived
    solver.add(total == required_days[city])

# Solve the problem
result = solver.check()
if result == sat:
    model = solver.model()
    for i in range(25):
        print(f"Day {i+1}: {model[days[i]]}")
else:
    print("No solution exists")