import z3

# Define cities and their IDs
cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 3, 4],  # Porto can fly to Prague, Santorini, Amsterdam
    1: [0, 2, 3, 4, 5],  # Prague can fly to Porto, Reykjavik, Santorini, Amsterdam, Munich
    2: [1, 3, 4, 5],  # Reykjavik can fly to Prague, Santorini, Amsterdam, Munich
    3: [0, 1, 2, 4, 5],  # Santorini can fly to Porto, Prague, Reykjavik, Amsterdam, Munich
    4: [0, 1, 2, 3, 5],  # Amsterdam can fly to Porto, Prague, Reykjavik, Santorini, Munich
    5: [1, 2, 4]  # Munich can fly to Prague, Reykjavik, Amsterdam
}

# Create variables for each day (1 to 16)
days = [z3.Int(f'd_{i}') for i in range(1, 17)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Porto
s.add(z3.Count(1, days) == 4)  # Prague
s.add(z3.Count(2, days) == 4)  # Reykjavik
s.add(z3.Count(3, days) == 2)  # Santorini
s.add(z3.Count(4, days) == 2)  # Amsterdam
s.add(z3.Count(5, days) == 4)  # Munich

# Add event constraints
# Days 4 to 7 must be in Reykjavik (indices 3 to 6)
for i in range(3, 7):
    s.add(days[i] == 2)
# Days 7 to 10 must be in Munich (indices 6 to 9)
for i in range(6, 10):
    s.add(days[i] == 5)
# Days 14 and 15 must be in Amsterdam (indices 13 and 14)
s.add(days[13] == 4)
s.add(days[14] == 4)

# Add transition constraints between consecutive days
for i in range(16):
    current_day = days[i]
    next_day = days[i+1] if i < 15 else None
    if i < 15:
        for a in range(6):
            s.add(z3.Implies(current_day == a,
                              z3.Or([next_day == a] + [next_day == b for b in adj[a]])))

# Solve the model
result = s.check()
if result == z3.sat:
    model = s.model()
    schedule = [model[day].as_long() for day in days]
    city_schedule = [cities[idx] for idx in schedule]
    for i, city in enumerate(city_schedule, 1):
        print(f"Day {i}: {city}")
else:
    print("No solution exists due to conflicting constraints.")