import z3

# Define cities and their IDs
cities = ['Helsinki', 'Prague', 'Valencia', 'Dubrovnik', 'Porto', 'Reykjavik']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 5],     # Helsinki can fly to Prague (1) and Reykjavik (5)
    1: [0, 2, 5],  # Prague can fly to Helsinki (0), Valencia (2), Reykjavik (5)
    2: [1, 3],     # Valencia can fly to Prague (1) and Porto (3)
    3: [2],        # Dubrovnik can fly to Helsinki (0)
    4: [2],        # Porto can fly to Valencia (2)
    5: [0, 1]      # Reykjavik can fly to Helsinki (0) and Prague (1)
}

# Create variables for each day (1 to 18)
days = [z3.Int(f'd_{i}') for i in range(1, 19)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Helsinki
s.add(z3.Count(1, days) == 3)  # Prague
s.add(z3.Count(2, days) == 5)  # Valencia
s.add(z3.Count(3, days) == 4)  # Dubrovnik
s.add(z3.Count(4, days) == 3)  # Porto
s.add(z3.Count(5, days) == 4)  # Reykjavik

# Add event constraints
# Days 16, 17, and 18 must be in Porto (indices 15, 16, 17)
for i in range(15, 18):
    s.add(days[i] == 4)

# Add transition constraints between consecutive days
for i in range(18):
    current_day = days[i]
    next_day = days[i+1] if i < 17 else None
    if i < 17:
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