import z3

# Define cities and their IDs
cities = ['Riga', 'Budapest', 'Paris', 'Warsaw']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3],  # Riga can fly to Budapest, Paris, Warsaw
    1: [3],        # Budapest can fly to Paris
    2: [0],        # Paris can fly to Riga
    3: [0, 1, 2]   # Warsaw can fly to Riga, Budapest, Paris
}

# Create variables for each day (1 to 17)
days = [z3.Int(f'd_{i}') for i in range(1, 18)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-3)
for d in days:
    s.add(z3.And(d >= 0, d < 4))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 7)  # Riga
s.add(z3.Count(1, days) == 7)  # Budapest
s.add(z3.Count(2, days) == 4)  # Paris
s.add(z3.Count(3, days) == 2)  # Warsaw

# Add event constraints
# Days 1 and 2 must be in Warsaw (indices 0 and 1)
s.add(days[0] == 3)
s.add(days[1] == 3)

# Days 11 to 17 must be in Riga (indices 10 to 16)
for i in range(10, 17):
    s.add(days[i] == 0)

# Add transition constraints between consecutive days
for i in range(17):
    current_day = days[i]
    next_day = days[i+1] if i < 16 else None
    if i < 16:
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