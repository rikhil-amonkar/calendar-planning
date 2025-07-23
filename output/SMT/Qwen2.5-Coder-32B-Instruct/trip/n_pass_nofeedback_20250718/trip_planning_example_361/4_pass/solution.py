from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each day
madrid_days = [Bool(f'madrid_day_{i}') for i in range(1, 16)]
seville_days = [Bool(f'seville_day_{i}') for i in range(1, 16)]
paris_days = [Bool(f'paris_day_{i}') for i in range(1, 16)]
bucharest_days = [Bool(f'bucharest_day_{i}') for i in range(1, 16)]

# Constraints
# Stay in Madrid from day 1 to day 7
for i in range(1, 8):
    solver.add(madrid_days[i-1] == True)

# Stay in Bucharest from day 14 to day 15
for i in range(14, 16):
    solver.add(bucharest_days[i-1] == True)

# Stay in Seville for 3 days
solver.add(Sum([If(seville_days[i-1], 1, 0) for i in range(1, 16)]) == 3)

# Stay in Paris for 6 days
solver.add(Sum([If(paris_days[i-1], 1, 0) for i in range(1, 16)]) == 6)

# Ensure no overlapping stays
for i in range(1, 16):
    solver.add(Or(madrid_days[i-1] == False, seville_days[i-1] == False, paris_days[i-1] == False, bucharest_days[i-1] == False))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(1, 16):
        if model.evaluate(madrid_days[i-1]):
            itinerary.append({"day": i, "place": "Madrid"})
        elif model.evaluate(seville_days[i-1]):
            itinerary.append({"day": i, "place": "Seville"})
        elif model.evaluate(paris_days[i-1]):
            itinerary.append({"day": i, "place": "Paris"})
        elif model.evaluate(bucharest_days[i-1]):
            itinerary.append({"day": i, "place": "Bucharest"})
    print(itinerary)