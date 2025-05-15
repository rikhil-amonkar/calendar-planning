from z3 import *

# Define the cities
cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]

# Required days for each city
required_days = {
    "Riga": 2,
    "Frankfurt": 3,
    "Amsterdam": 2,
    "Vilnius": 5,
    "London": 2,
    "Stockholm": 3,
    "Bucharest": 4
}

# Create a variable for each day
days = [String(f"day_{i+1}") for i in range(15)]

# Initialize solver
solver = Solver()

# Define the direct flights as a set of pairs
direct_flights = {
    ("London", "Amsterdam"), ("Vilnius", "Frankfurt"),
    ("Riga", "Vilnius"), ("Riga", "Stockholm"),
    ("London", "Bucharest"), ("Amsterdam", "Stockholm"),
    ("Amsterdam", "Frankfurt"), ("Frankfurt", "Stockholm"),
    ("Bucharest", "Riga"), ("Amsterdam", "Riga"),
    ("Amsterdam", "Bucharest"), ("Riga", "Frankfurt"),
    ("Bucharest", "Frankfurt"), ("London", "Frankfurt"),
    ("London", "Stockholm")
}

# Add constraints for fixed time windows
solver.add(Or([days[1] == "Amsterdam", days[2] == "Amsterdam"]))  # Amsterdam on day 2 or 3

for i in range(6, 11):  # days 7-11 (indices 6 to 10)
    solver.add(days[i] == "Vilnius")

for i in range(12, 15):  # days 13-15 (indices 12 to 14)
    solver.add(days[i] == "Stockholm")

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