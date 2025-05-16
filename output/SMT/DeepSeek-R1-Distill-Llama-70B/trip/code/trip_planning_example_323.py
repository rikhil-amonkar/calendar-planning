import z3

# Define cities and their IDs
cities = ['Split', 'Oslo', 'London', 'Porto']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 3],    # Split can fly to Oslo (1) and London (3)
    1: [0, 2, 3], # Oslo can fly to Split (0), London (3), and Porto (2)
    2: [1, 3],    # London can fly to Oslo (1) and Split (3)
    3: [0, 1, 2]  # Porto can fly to Split (0), Oslo (1), and London (2)
}

# Create variables for each day (1 to 16)
days = [z3.Int(f'd_{i}') for i in range(1, 17)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-3)
for d in days:
    s.add(z3.And(d >= 0, d < 4))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Split
s.add(z3.Count(1, days) == 2)  # Oslo
s.add(z3.Count(2, days) == 7)  # London
s.add(z3.Count(3, days) == 5)  # Porto

# Add event constraints
# Days 1 to 7 must be in London (indices 0 to 6)
for i in range(7):
    s.add(days[i] == 2)

# Days 7 to 11 must be in Split (indices 6 to 10)
for i in range(6, 11):
    s.add(days[i] == 0)

# Add transition constraints between consecutive days
for i in range(16):
    current_day = days[i]
    next_day = days[i+1] if i < 15 else None
    if i < 15:
        for a in range(4):
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