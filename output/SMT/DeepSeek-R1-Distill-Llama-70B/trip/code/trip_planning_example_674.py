import z3

# Define cities and their IDs
cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [4, 1, 2, 3, 5],    # Helsinki can fly to Reykjavik (4), Warsaw (1), Madrid (2), Split (3), Budapest (5)
    1: [5, 4, 2, 3],        # Warsaw can fly to Budapest (5), Reykjavik (4), Madrid (2), Split (3)
    2: [5, 0, 1, 4],        # Madrid can fly to Budapest (5), Helsinki (0), Warsaw (1), Reykjavik (4)
    3: [1, 2, 4],           # Split can fly to Warsaw (1), Madrid (2), Reykjavik (4)
    4: [0, 1, 2, 5],        # Reykjavik can fly to Helsinki (0), Warsaw (1), Madrid (2), Budapest (5)
    5: [0, 1, 2, 4]         # Budapest can fly to Helsinki (0), Warsaw (1), Madrid (2), Reykjavik (4)
}

# Create variables for each day (1 to 14)
days = [z3.Int(f'd_{i}') for i in range(1, 15)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Helsinki
s.add(z3.Count(1, days) == 3)  # Warsaw
s.add(z3.Count(2, days) == 4)  # Madrid
s.add(z3.Count(3, days) == 4)  # Split
s.add(z3.Count(4, days) == 2)  # Reykjavik
s.add(z3.Count(5, days) == 4)  # Budapest

# Add event constraints
# Days 1 and 2 must be in Helsinki (indices 0 and 1)
s.add(days[0] == 0)
s.add(days[1] == 0)
# Days 9, 10, and 11 must be in Warsaw (indices 8, 9, and 10)
s.add(days[8] == 1)
s.add(days[9] == 1)
s.add(days[10] == 1)
# Days 8 and 9 must be in Reykjavik (indices 7 and 8)
s.add(days[7] == 4)
s.add(days[8] == 4)

# Add transition constraints between consecutive days
for i in range(14):
    current_day = days[i]
    next_day = days[i+1] if i < 13 else None
    if i < 13:
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