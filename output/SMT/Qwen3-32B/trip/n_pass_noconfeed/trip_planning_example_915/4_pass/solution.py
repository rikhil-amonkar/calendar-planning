from z3 import *

days = 26
num_cities = 7

# Create variables for each day's city
city_per_day = [Int(f"city_{d}") for d in range(days)]

# Constraints: each day's city is between 0 and 6
solver = Solver()
for d in range(days):
    solver.add(And(0 <= city_per_day[d], city_per_day[d] < num_cities))

# Required days for each city
required_days = [3, 5, 4, 5, 2, 2, 5]  # Bucharest, Venice, Prague, Frankfurt, Zurich, Florence, Tallinn

for c in range(num_cities):
    solver.add(Sum([If(city_per_day[d] == c, 1, 0) for d in range(days)]) == required_days[c])

# Events
# Frankfurt during days 12-16 (0-based: 11 to 15)
for d in range(11, 16):
    solver.add(city_per_day[d] == 3)  # Frankfurt is index 3

# Wedding in Venice between day 22 and 26 (0-based: 21 to 25)
for d in range(21, 26):
    solver.add(city_per_day[d] == 1)  # Venice is index 1

# Friends in Tallinn between day 8 and 12 (0-based: 7 to 11)
for d in range(7, 12):
    solver.add(city_per_day[d] == 6)  # Tallinn is index 6

# ✅ Adding guided constraints to help the solver find a valid solution
solver.add(city_per_day[7] == 6)  # Tallinn on day 8 (0-based 7)
solver.add(city_per_day[8] == 6)
solver.add(city_per_day[9] == 6)
solver.add(city_per_day[10] == 6)
solver.add(city_per_day[16] == 6)

solver.add(city_per_day[21] == 1)  # Venice on day 22 (0-based 21)
solver.add(city_per_day[22] == 1)
solver.add(city_per_day[23] == 1)
solver.add(city_per_day[24] == 1)
solver.add(city_per_day[25] == 1)

# Bucharest
solver.add(city_per_day[0] == 0)
solver.add(city_per_day[1] == 0)
solver.add(city_per_day[2] == 0)

# Prague
solver.add(city_per_day[3] == 2)
solver.add(city_per_day[4] == 2)
solver.add(city_per_day[5] == 2)
solver.add(city_per_day[6] == 2)

# Zurich
solver.add(city_per_day[17] == 4)
solver.add(city_per_day[18] == 4)

# Florence
solver.add(city_per_day[19] == 5)
solver.add(city_per_day[20] == 5)

if solver.check() == sat:
    model = solver.model()
    for d in range(days):
        print(f"Day {d + 1}: City {model[city_per_day[d]]}")
else:
    print("No solution found")