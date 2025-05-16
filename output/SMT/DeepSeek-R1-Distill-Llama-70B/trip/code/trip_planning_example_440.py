import z3

# Define cities and their IDs
cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 4],  # Split can fly to Helsinki (1) and Geneva (4)
    1: [0, 2, 3, 4],  # Helsinki can fly to Split (0), Reykjavik (2), Vilnius (3), Geneva (4)
    2: [1],  # Reykjavik can fly to Helsinki (1)
    3: [1, 4],  # Vilnius can fly to Helsinki (1) and Geneva (4)
    4: [0, 1, 3]  # Geneva can fly to Split (0), Helsinki (1), Vilnius (3)
}

# Create variables for each day (1 to 12)
days = [z3.Int(f'd_{i}') for i in range(1, 13)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-4)
for d in days:
    s.add(z3.And(d >= 0, d < 5))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Split
s.add(z3.Count(1, days) == 2)  # Helsinki
s.add(z3.Count(2, days) == 3)  # Reykjavik
s.add(z3.Count(3, days) == 3)  # Vilnius
s.add(z3.Count(4, days) == 6)  # Geneva

# Add event constraints
# Days 1 and 2 must be in Split (indices 0 and 1)
s.add(days[0] == 0)
s.add(days[1] == 0)
# Days 7-9 must be in Vilnius (indices 6-8)
for i in range(6, 9):
    s.add(days[i] == 3)
# Days 10-12 must be in Reykjavik (indices 9-11)
for i in range(9, 12):
    s.add(days[i] == 2)

# Add transition constraints between consecutive days
for i in range(12):
    current_day = days[i]
    next_day = days[i+1] if i < 11 else None
    if i < 11:
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