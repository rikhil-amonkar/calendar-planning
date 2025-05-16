import z3

# Define cities and their IDs
cities = ['Naples', 'Seville', 'Milan']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2],  # Naples can fly to Milan
    1: [2],  # Seville can fly to Milan
    2: [0, 1]  # Milan can fly to Naples and Seville
}

# Create variables for each day (1 to 12)
days = [z3.Int(f'd_{i}') for i in range(1, 13)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-2)
for d in days:
    s.add(z3.And(d >= 0, d < 3))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Naples
s.add(z3.Count(1, days) == 4)  # Seville
s.add(z3.Count(2, days) == 7)  # Milan

# Add event constraint: days 9 to 12 must be in Seville (indices 8 to 11)
for i in range(8, 12):
    s.add(days[i] == 1)

# Add transition constraints between consecutive days
for i in range(12):
    current_day = days[i]
    next_day = days[i+1] if i < 11 else None
    if i < 11:
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