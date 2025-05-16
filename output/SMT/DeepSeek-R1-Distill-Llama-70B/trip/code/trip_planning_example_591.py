import z3

# Define cities and their IDs
cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [4],           # Stuttgart can fly to Munich
    1: [3, 4],        # Bucharest can fly to Valencia and Munich
    2: [4, 3],        # Geneva can fly to Munich and Valencia
    3: [1, 2, 0, 4], # Valencia can fly to Bucharest, Geneva, Stuttgart, and Munich
    4: [0, 1, 2, 3]  # Munich can fly to Stuttgart, Bucharest, Geneva, and Valencia
}

# Create variables for each day (1 to 17)
days = [z3.Int(f'd_{i}') for i in range(1, 18)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-4)
for d in days:
    s.add(z3.And(d >= 0, d < 5))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Stuttgart
s.add(z3.Count(1, days) == 2)  # Bucharest
s.add(z3.Count(2, days) == 4)  # Geneva
s.add(z3.Count(3, days) == 6)  # Valencia
s.add(z3.Count(4, days) == 7)  # Munich

# Add event constraints
# Days 1 to 4 must be in Geneva (indices 0 to 3)
for i in range(4):
    s.add(days[i] == 2)

# Days 4 to 10 must be in Munich (indices 3 to 9)
for i in range(3, 10):
    s.add(days[i] == 4)

# Add transition constraints between consecutive days
for i in range(17):
    current_day = days[i]
    next_day = days[i+1] if i < 16 else None
    if i < 16:
        for a in range(5):
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