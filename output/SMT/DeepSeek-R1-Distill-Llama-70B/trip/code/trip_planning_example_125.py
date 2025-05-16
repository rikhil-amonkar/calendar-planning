import z3

# Define cities and their IDs
cities = ['Stuttgart', 'Seville', 'Manchester']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2],      # Stuttgart can fly to Manchester
    1: [2],      # Seville can fly to Manchester
    2: [0, 1]    # Manchester can fly to Stuttgart and Seville
}

# Create variables for each day (1 to 15)
days = [z3.Int(f'd_{i}') for i in range(1, 16)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-2)
for d in days:
    s.add(z3.And(d >= 0, d < 3))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 6)  # Stuttgart
s.add(z3.Count(1, days) == 7)  # Seville
s.add(z3.Count(2, days) == 4)  # Manchester

# Add event constraint: days 1 to 6 must be in Stuttgart (indices 0 to 5)
for i in range(6):
    s.add(days[i] == 0)

# Add transition constraints between consecutive days
for i in range(15):
    current_day = days[i]
    next_day = days[i+1] if i < 14 else None
    if i < 14:
        for a in range(3):
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